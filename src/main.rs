use anyhow::{anyhow, Context, Result};
use bumpalo::Bump;
use core::fmt;
use linkedlist::LinkedList;
use regex::Regex;
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    env,
    fmt::{Debug, Display},
    fs::File,
    hash::Hash,
    io::Read,
    process, u32,
};

mod linkedlist;

type Id = u32;

/*
 * A simple graph node with adjacency list
 */
struct Node<'a> {
    id: Id,
    // RefCell to enable interior mutability
    neighbors: RefCell<Vec<Edge<'a>>>,
}

/*
 * Default formatter : display only id
 */
impl<'a> Display for Node<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.id)
    }
}

/*
 * Debug formatter : display all neighbors with weights
 */
impl<'a> Debug for Node<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for neighbor in self.neighbors.borrow().iter() {
            writeln!(f, "{}{}", self.id, neighbor)?;
        }
        Ok(())
    }
}

impl<'a> PartialEq for Node<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<'a> Hash for Node<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl<'a> Eq for Node<'a> {}

impl<'a> PartialOrd for Node<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.id.partial_cmp(&other.id)
    }
}

impl<'a> Ord for Node<'a> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

/*
 * "Edge" : not really an edge (u,v) with u,v nodes.
 * An Edge is owned by a node and represents a neighbor with the weight of the edge.
 */
#[derive(PartialEq, Eq)]
struct Edge<'a> {
    neighbor: &'a Node<'a>,
    weight: u32,
}

/*
 * Display ---<weight>---<neighbor id>
 */
impl<'a> Display for Edge<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "-{:->3}-{:->3}", self.weight, self.neighbor.id)
    }
}

impl<'a> PartialOrd for Edge<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.weight.cmp(&other.weight))
    }
}

impl<'a> Ord for Edge<'a> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.weight.cmp(&other.weight)
    }
}

/*
 * The cost and full path (as a linked list) of a shortest path
 */
struct ShortestPath<'a> {
    path: Option<Box<LinkedList<&'a Node<'a>>>>,
    cost: u32,
}

/*
 * The cost and full path (as a linked list) of a shortest path
 */
impl<'a> Display for ShortestPath<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Cost: {}\nPath:", self.cost)?;
        let mut curr_opt: &Option<Box<LinkedList<&'a Node<'a>>>> = &self.path;
        while let Some(curr) = curr_opt {
            write!(f, "{} ", curr.value)?;
            curr_opt = &curr.next;
        }
        Ok(())
    }
}

/*
 * Representing an undirected graph as a hashmap of nodes,
 * each with their adjacency list.
 */
struct Graph<'a> {
    nodes: HashMap<Id, &'a Node<'a>>,
}

/*
 * Display all nodes with their neighbors
 */
impl<'a> Display for Graph<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        for (_id, node) in &self.nodes {
            writeln!(f, "Node {} : ", node)?;
            writeln!(f, "{:?}", node)?;
        }
        Ok(())
    }
}

impl<'a> Graph<'a> {
    /*
     * Parse graph from input.
     * Input should be a list of lines, each formatted as follows :
     * <node A>-<weight>-<node B>
     *
     * <bump> is the arena allocator from where all nodes will be allocated
     */
    fn parse(input: &str, bump: &'a Bump) -> Result<Self> {
        let mut res = Graph {
            nodes: HashMap::new(),
        };

        // Parse line after line : {node a}-{weight}-{node b}
        let re = Regex::new(r"(\d+)-(\d+)-(\d+)")?;
        for l in input.lines() {
            let captures = re
                .captures(l)
                .ok_or(anyhow!("Failed to parse line {}", l))?;
            let id_a: Id = captures.get(1).unwrap().as_str().parse()?;
            let weight: u32 = captures.get(2).unwrap().as_str().parse()?;
            let id_b: Id = captures.get(3).unwrap().as_str().parse()?;

            // Add nodes if needed
            if !res.nodes.contains_key(&id_a) {
                // Use arena to ensure all nodes have the same lifetime
                res.nodes.insert(
                    id_a,
                    bump.alloc(Node {
                        id: id_a,
                        neighbors: RefCell::new(vec![]),
                    }),
                );
            }
            if !res.nodes.contains_key(&id_b) {
                res.nodes.insert(
                    id_b,
                    bump.alloc(Node {
                        id: id_b,
                        neighbors: RefCell::new(vec![]),
                    }),
                );
            }

            // Add neighbor
            let node_a = res.nodes.get(&id_a).unwrap();
            let node_b = res.nodes.get(&id_b).unwrap();
            let mut neighbors_a = node_a.neighbors.borrow_mut();
            neighbors_a.push(Edge {
                neighbor: node_b,
                weight,
            });
            let mut neighbors_b = node_b.neighbors.borrow_mut();
            neighbors_b.push(Edge {
                neighbor: node_a,
                weight,
            });
        }

        Ok(res)
    }

    /*
     * Dijkstra algorithm : computes the shortest path from
     * <start> node to <dst> node.
     */
    fn dijkstra(&self, start: &'a Node<'a>, dst: &'a Node<'a>) -> Option<ShortestPath<'a>> {
        let mut prev = HashMap::<&'a Node<'a>, (u32, Option<&'a Node<'a>>)>::new();
        let mut tovisit = HashSet::<&'a Node<'a>>::new();

        // At first, all nodes have max cost except for start node
        for node in self.nodes.values() {
            prev.insert(node, (u32::MAX, None));
        }
        prev.get_mut(start)?.0 = 0;

        // At first, every node is to visit
        for node in self.nodes.values() {
            tovisit.insert(node);
        }

        // Pick the closest unvisited node
        while let Some(node) = {
            let mut min_distance = u32::MAX;
            let mut lowest = None;
            for node in &tovisit {
                let (dist, _prev) = prev.get(node)?;
                if *dist < min_distance {
                    lowest = Some(node);
                    min_distance = *dist;
                }
            }
            // Move picked node out of hashmap
            let lowest = lowest.cloned();
            if let Some(node) = lowest {
                tovisit.remove(node);
            }
            lowest
        } {
            // Update distance and previous node if needed
            let distance = prev.get(node)?.0;
            for edge in node.neighbors.borrow().iter() {
                let curr_prev = prev.get_mut(edge.neighbor)?;
                let challenger_distance = distance + edge.weight;
                // If recorded distance is larger than new distance, update
                if challenger_distance < curr_prev.0 {
                    let mut curr_prev = prev.remove(edge.neighbor)?;
                    curr_prev.0 = challenger_distance;
                    curr_prev.1 = Some(node);
                    prev.insert(edge.neighbor, curr_prev);
                }
            }
        }

        // Finally, create a linked list with final path
        let mut path = LinkedList::new(dst);
        let mut curr_opt = prev.get(dst).and_then(|x| Some(x.1))?;
        while let Some(curr) = curr_opt {
            path = path.push_front(curr);
            curr_opt = prev.get(curr).and_then(|x| x.1);
        }
        let cost = prev.get(dst).and_then(|x| Some(x.0))?;

        Some(ShortestPath {
            cost,
            path: Some(Box::new(path)),
        })
    }
}

fn main() -> Result<()> {
    println!("Simple graph shortest path poc in rust :D");
    if env::args().len() != 4 {
        println!(
            "Usage : {} [graph input file] [start node] [dst node]",
            env::args().next().unwrap()
        );
        process::exit(1);
    }
    let mut args = env::args().skip(1);

    let path = args.next().unwrap();
    let mut f = File::open(path).context("Failed to open file")?;
    let mut input = String::new();
    f.read_to_string(&mut input)
        .context("Failed to read file")?;

    let bump = Bump::new();
    let g = Graph::parse(&input, &bump).context("Failed to create graph")?;
    println!("Parsed graph :\n{}", g);

    let get_node = |node| {
        g.nodes
            .get(node)
            .ok_or(anyhow!("Failed to find node {}", node))
    };
    let start: u32 = args.next().unwrap().parse()?;
    let dst: u32 = args.next().unwrap().parse()?;
    let start = get_node(&start)?;
    let dst = get_node(&dst)?;
    let shortest_path = g
        .dijkstra(start, dst)
        .ok_or(anyhow!("Failed to find shortest path !"))?;
    println!("{}", shortest_path);

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_graph() {
        let input = "0-4-1
1-8-2
2-7-0";
        let bump = Bump::new();
        let g = Graph::parse(&input, &bump).unwrap();
        assert_eq!(g.nodes.get(&1).and_then(|x| Some(x.id)), Some(1));
        assert_eq!(
            g.nodes
                .get(&0)
                .and_then(|x| Some(x.neighbors.borrow().iter().fold(0, |acc, edge| {
                    acc + ((edge.neighbor.id == 2) as u32) * edge.weight
                }))),
            Some(7)
        );
    }

    #[test]
    fn dijkstra() {
        let input = "0-4-1
0-8-7
1-8-2
1-11-7
2-7-3
2-4-5
2-2-8
3-9-4
3-14-5
4-10-5
5-2-6
6-1-7
6-6-8
7-7-8";
        let bump = Bump::new();
        let g = Graph::parse(&input, &bump).unwrap();
        let start = g.nodes.get(&0).unwrap();
        let dst = g.nodes.get(&5).unwrap();
        let shortest_path = g.dijkstra(start, dst).unwrap();
        assert_eq!(shortest_path.cost, 11);
        assert_eq!(
            shortest_path
                .path
                .and_then(|prev| prev.next.and_then(|prev| Some(prev.value.id))),
            Some(7)
        );
    }
}
