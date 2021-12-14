use routecore::addr::Prefix;

use donkey_mule_horse::trie::DonkeyTrie;

#[derive(Debug)]
struct RisWhoisDumpIpv4Item {
    origin: u32,
    prefix: Prefix,
    n_ris_peers: u16,
}

pub fn main() {}

#[cfg(test)]
mod tests {
    use std::{
        net::{IpAddr, Ipv4Addr},
        str::FromStr,
        time::{Duration, Instant},
    };

    use donkey_mule_horse::trie::DonkeyTrieNode;
    use num_format::{Locale, ToFormattedString};
    use routecore::addr::Prefix;

    use super::*;

    #[test]
    fn donkey_binary_trie_with_sample_data() {
        let mut tree = DonkeyTrie::<String>::new();
        tree.push(0b01u32 << 30, 2).set_meta("[01]".to_string());
        tree.push(0b10u32 << 30, 2).set_meta("[10]".to_string());
        tree.push(0b000u32 << 29, 3).set_meta("[000]".to_string());
        tree.push(0b110u32 << 29, 3).set_meta("[110]".to_string());
        tree.push(0b111u32 << 29, 3).set_meta("[111]".to_string());
        tree.push(0b11001u32 << 27, 5)
            .set_meta("[11001]".to_string());

        tree.print();
    }

    // See: https://en.wikipedia.org/wiki/Longest_prefix_match
    #[test]
    fn donkey_binary_trie_longest_prefix_match_wikipedia() {
        let mut tree = DonkeyTrie::<String>::new();

        let prefix = Prefix::from_str("192.168.20.16/28").unwrap();
        if let IpAddr::V4(ipv4) = prefix.addr() {
            let bits = u32::from_be_bytes(ipv4.octets());
            tree.push(bits, prefix.len())
                .set_meta("192.168.20.16/28".to_string());
        }

        let prefix = Prefix::from_str("192.168.0.0/16").unwrap();
        if let IpAddr::V4(ipv4) = prefix.addr() {
            let bits = u32::from_be_bytes(ipv4.octets());
            tree.push(bits, prefix.len())
                .set_meta("192.168.0.0/16".to_string());
        }

        tree.print();

        let search_prefix = Prefix::from_str("192.168.20.19/32").unwrap();
        if let (IpAddr::V4(ipv4), len) = search_prefix.addr_and_len() {
            let bits = u32::from_be_bytes(ipv4.octets());
            let (_found_prefix, _found_len, found_meta) = tree.longest_match(bits, len).unwrap();
            assert_eq!(found_meta, Some(&"192.168.20.16/28".to_string()));
        }
    }

    // See: https://d-nb.info/1104374552/34
    #[test]
    fn donkey_binary_trie_longest_prefix_match_paper_1104374552_slash_34() {
        let mut tree = DonkeyTrie::<String>::new();
        tree.push(0b0000u32 << 28, 4).set_meta("P1".to_string());
        tree.push(0b0000_111u32 << 25, 7).set_meta("P2".to_string());
        tree.push(0b0000_1111_0000u32 << 20, 12)
            .set_meta("P3".to_string());

        tree.print();

        let bits = 0b0000_0110_1111u32 << 20;
        let (_found_prefix, _found_len, found_meta) = tree.longest_match(bits, 12).unwrap();
        assert_eq!(found_meta, Some(&"P1".to_string()));

        let bits = 0b0000_1111_0000u32 << 20;
        let (_found_prefix, _found_len, found_meta) = tree.longest_match(bits, 12).unwrap();
        assert_eq!(found_meta, Some(&"P3".to_string()));
    }

    #[test]
    #[allow(non_snake_case)]
    fn donkey_binary_trie_with_RISwhois_IPv4_data_sample() {
        let riswhoisdump_ipv4_fragment = r#"
            174	0.0.0.0/0	6
            2519	1.1.96.0/24	347
            23969	1.1.208.0/21	406
            9583	1.6.96.0/22	358
            9583	1.6.100.0/22	358
            23969	1.20.149.0/24	396
        "#;

        let mut tree = DonkeyTrie::<String>::new();
        for line in riswhoisdump_ipv4_fragment.lines() {
            if !line.trim().is_empty() && !line.starts_with('%') {
                let item = parse_RISwhois_dump_IPv4_line(line).unwrap();
                insert_RISwhois_IPv4_item(&item, &mut tree).unwrap();
            }
        }

        tree.print();
    }

    /// To see the performance report run with:
    ///   cargo test --release -- tests::donkey_binary_trie_with_RISwhois_IPv4_data_full --exact --nocapture
    #[test]
    #[allow(non_snake_case)]
    fn donkey_binary_trie_with_RISwhois_IPv4_data_full() {
        time_graph::enable_data_collection(true);

        let mut tree = DonkeyTrie::<String>::new();
        let mut table = ip_network_table::IpNetworkTable::new();
        let strides = vec![4, 4, 4, 4, 4, 4, 4, 4];
        let mut tree_bitmap: trie::treebitmap_univec::TreeBitMap<u32, trie::common::NoMeta> =
            trie::treebitmap_univec::TreeBitMap::new(strides.clone());
        let mut trie = trie::simpletrie::TrieNode::new(false);
        type StoreType = rotonda_store::InMemStorage<u32, rotonda_store::common::NoMeta>;
        let mut rotonda_store = rotonda_store::TreeBitMap::<StoreType>::new(strides);

        println!("Loading... ");
        let start = Instant::now();
        let data = std::fs::read_to_string("./riswhoisdump.IPv4").unwrap();
        let loading_time = start.elapsed();
        let line_count = data.lines().count();

        println!("Parsing... ");
        let start = Instant::now();
        let data = data
            .lines()
            .filter(|line| !line.trim().is_empty() && !line.starts_with('%'))
            .map(|line| parse_RISwhois_dump_IPv4_line(line))
            .filter(|item_result| item_result.is_ok())
            .collect::<Vec<_>>();
        let parsing_time = start.elapsed();
        let record_count = data.len();

        println!("Inserting: DonkeyTrie ...");
        for item_result in &data {
            let item = item_result.as_ref().unwrap();
            insert_RISwhois_IPv4_item(item, &mut tree).unwrap();
        }

        println!("Inserting: ip_network_table ...");
        for item_result in &data {
            let prefix = item_result.as_ref().unwrap().prefix;
            let network = ip_network::IpNetwork::new(prefix.addr(), prefix.len()).unwrap();
            let _ = table.insert(network, "foo");
        }

        println!("Inserting: trie::TreeBitMap ...");
        for item_result in &data {
            let prefix = item_result.as_ref().unwrap().prefix;
            if let IpAddr::V4(ipv4) = prefix.addr() {
                let bits = u32::from_be_bytes(ipv4.octets());
                let trie_prefix = trie::common::Prefix::new(bits, prefix.len());
                tree_bitmap.insert(trie_prefix);
            }
        }

        fn simpletrie_push(
            mut cursor: &mut trie::simpletrie::TrieNode,
            pfx: trie::simpletrie::Prefix<trie::simpletrie::NoMeta>,
        ) {
            let mut first_bit = pfx.net;
            let mut built_prefix: u32 = 0;

            for _ in 0..pfx.len {
                match first_bit.leading_ones() {
                    0 => {
                        if !cursor.left.is_some() {
                            cursor.left = Some(Box::new(trie::simpletrie::TrieNode::new(false)))
                        };
                        built_prefix = built_prefix << 1;
                        cursor = cursor.left.as_deref_mut().unwrap();
                    }
                    1..=32 => {
                        if !cursor.right.is_some() {
                            cursor.right = Some(Box::new(trie::simpletrie::TrieNode::new(false)));
                        }
                        cursor = cursor.right.as_deref_mut().unwrap();
                        built_prefix = built_prefix << 1 | 1;
                    }
                    _ => {
                        panic!("illegal prefix encountered. Giving up.");
                    }
                }
                first_bit = first_bit << 1;
            }

            cursor.prefix = true;
        }

        println!("Inserting: trie::simpletrie ...");
        for item_result in &data {
            let prefix = item_result.as_ref().unwrap().prefix;
            if let IpAddr::V4(ipv4) = prefix.addr() {
                let bits = u32::from_be_bytes(ipv4.octets());
                let simpletrie_prefix = trie::simpletrie::Prefix::new(bits, prefix.len());
                simpletrie_push(&mut trie, simpletrie_prefix);
            }
        }

        println!("Inserting: rotonda_store::TreeBitMap ...");
        for item_result in &data {
            let prefix = item_result.as_ref().unwrap().prefix;
            if let IpAddr::V4(ipv4) = prefix.addr() {
                let bits = u32::from_be_bytes(ipv4.octets());
                let rotonda_prefix = rotonda_store::common::Prefix::new(bits, prefix.len());
                rotonda_store.insert(rotonda_prefix).unwrap();
            }
        }

        #[time_graph::instrument]
        fn alt_longest_match<'a, T>(
            table: &'a ip_network_table::IpNetworkTable<T>,
            prefix: &Prefix,
        ) -> (ip_network::IpNetwork, &'a T) {
            table.longest_match(prefix.addr()).unwrap()
        }

        #[time_graph::instrument]
        fn treebitmap_longest_match<'a, AF, T>(
            tree_bitmap: &'a trie::treebitmap_univec::TreeBitMap<AF, T>,
            prefix: &trie::common::Prefix<AF, trie::common::NoMeta>,
        ) -> Vec<&'a trie::common::Prefix<AF, T>>
        where
            AF: trie::common::AddressFamily + From<u32>,
            T: std::fmt::Debug,
        {
            tree_bitmap.match_longest_prefix(prefix)
        }

        #[time_graph::instrument]
        pub fn simple_trie_longest_matching_prefix<'a>(
            search_pfx: &'a trie::simpletrie::Prefix<trie::simpletrie::NoMeta>,
            trie: &'a trie::simpletrie::TrieNode,
        ) -> trie::simpletrie::Prefix<trie::simpletrie::NoMeta> {
            let mut cursor: &'a trie::simpletrie::TrieNode = trie;
            let mut cursor_pfx: u32 = 0;
            let mut match_pfx: u32 = 0;
            let mut match_len = 0;
            let mut first_bit = search_pfx.net;

            for i in 1..=search_pfx.len {
                match first_bit.leading_ones() {
                    0 => {
                        if cursor.left.is_some() {
                            cursor = cursor.left.as_deref().unwrap();
                            cursor_pfx = cursor_pfx << 1;
                            if cursor.prefix == true {
                                match_pfx = cursor_pfx;
                                match_len = i;
                                // println!(
                                //     "lmp less-specific: {:?}/{}",
                                //     std::net::Ipv4Addr::from(match_pfx << (32 - match_len)),
                                //     match_len
                                // );
                            }
                        } else {
                            break;
                        }
                    }
                    b if b >= 1 => {
                        if cursor.right.is_some() {
                            cursor = cursor.right.as_deref().unwrap();
                            cursor_pfx = cursor_pfx << 1 | 1;
                            if cursor.prefix == true {
                                match_pfx = cursor_pfx;
                                match_len = i;
                                // println!(
                                //     "lmp less-specific: {:?}/{}",
                                //     std::net::Ipv4Addr::from(match_pfx << (32 - match_len)),
                                //     match_len
                                // );
                            }
                        } else {
                            break;
                        }
                    }
                    _ => {
                        panic!("illegal prefix encountered. Giving up.");
                    }
                }
                first_bit = first_bit << 1;
            }

            if match_len > 0 {
                trie::simpletrie::Prefix::new(match_pfx << (32 - match_len), match_len)
            } else {
                trie::simpletrie::Prefix::new(0, 0)
            }
        }

        #[time_graph::instrument]
        fn rotonda_store_longest_match<'a>(
            rotonda_store: &'a rotonda_store::TreeBitMap<StoreType>,
            prefix: &rotonda_store::common::Prefix<u32, rotonda_store::common::NoMeta>,
        ) -> rotonda_store::QueryResult<
            'a,
            rotonda_store::InMemStorage<u32, rotonda_store::common::NoMeta>,
        > {
            rotonda_store.match_prefix(
                prefix,
                &rotonda_store::MatchOptions {
                    match_type: rotonda_store::MatchType::LongestMatch,
                    include_less_specifics: false,
                    include_more_specifics: true,
                },
            )
        }

        // testing
        println!("Finding and comparing longest matching prefixes:");
        for item in &data {
            let item = item.as_ref().unwrap();
            let prefix = item.prefix;

            if let (IpAddr::V4(ipv4), len) = prefix.addr_and_len() {
                let bits = u32::from_be_bytes(ipv4.octets());
                let (our_prefix, our_len, _) = tree.longest_match(bits, len).unwrap();
                let our_prefix = Prefix::new_v4(Ipv4Addr::from(our_prefix), our_len).unwrap();
                let (their_prefix, _) = alt_longest_match(&table, &prefix);
                assert_eq!(their_prefix.to_string(), our_prefix.to_string(), "Our DonkeyTrie LMP search for '{}' doesn't agree with the ip_network_table crate", prefix);

                let mut more_specific = false;
                let rotonda_store_search_prefix =
                    rotonda_store::common::Prefix::new(bits, prefix.len());
                let rotonda_store_prefix =
                    rotonda_store_longest_match(&rotonda_store, &rotonda_store_search_prefix);
                let rotonda_store_prefix_str = match (
                    &rotonda_store_prefix.prefix,
                    &rotonda_store_prefix.more_specifics,
                ) {
                    (Some(exact), None) => format!("{:?}", exact).replace(" with None", ""),
                    (Some(exact), Some(more)) => {
                        let mut r = vec![*exact];
                        r.extend_from_slice(more.as_slice());
                        let search_prefix = if let IpAddr::V4(ipv4) = their_prefix.network_address()
                        {
                            let bits = u32::from_be_bytes(ipv4.octets());
                            rotonda_store::common::Prefix::new(bits, their_prefix.netmask())
                        } else {
                            unimplemented!()
                        };
                        if r.contains(&&search_prefix) {
                            more_specific = true;
                            their_prefix.to_string()
                        } else {
                            "0.0.0.0/0".to_string()
                        }
                    }
                    _ => "0.0.0.0/0".to_string(),
                };
                assert_eq!(their_prefix.to_string(), rotonda_store_prefix_str, "Our Rotonda Store LMP search for '{}' doesn't agree with the ip_network_table crate (our full answer was: {:?})", prefix, rotonda_store_prefix);

                // match against ip_network_table only if the result is considered by Rotonda Store to be an exact match
                // otherwise match against the exact match that Rotonda Store found, because neither the treebitmap or
                // simple trie stores report a more specific as the result of a longest matching prefix search, so just
                // check that they agree with Rotonda Store instead.
                let expected_prefix_str = if more_specific {
                    let exact = rotonda_store_prefix.prefix.unwrap();
                    format!("{:?}", exact).replace(" with None", "")
                } else {
                    their_prefix.to_string()
                };

                let trie_search_prefix = trie::common::Prefix::new(bits, prefix.len());
                let trie_prefix = treebitmap_longest_match(&tree_bitmap, &trie_search_prefix);
                let trie_prefix_str = if trie_prefix.is_empty() {
                    "0.0.0.0/0".to_string()
                } else {
                    format!("{:?}", trie_prefix[trie_prefix.len() - 1]).replace(" with None", "")
                };
                assert_eq!(
                    expected_prefix_str,
                    trie_prefix_str,
                    "trie::BitMapTree LMP search for '{}' doesn't agree with the {}",
                    prefix,
                    if more_specific {
                        "Rotonda Store"
                    } else {
                        "ip_network_table crate"
                    }
                );

                let trie_search_prefix = trie::simpletrie::Prefix::new(bits, prefix.len());
                let trie_prefix = simple_trie_longest_matching_prefix(&trie_search_prefix, &trie);
                let trie_prefix_str = format!("{:?}", trie_prefix).replace(" -> None", "");
                assert_eq!(
                    expected_prefix_str,
                    trie_prefix_str,
                    "trie::simpletrie LMP search for '{}' doesn't agree with the {}",
                    prefix,
                    if more_specific {
                        "Rotonda Store"
                    } else {
                        "ip_network_table crate"
                    }
                );
            }
        }

        let graph = time_graph::get_full_graph();
        let our_insert = graph
            .spans()
            .filter(|&s| s.callsite.name() == "push")
            .next()
            .unwrap();
        let our_search = graph
            .spans()
            .filter(|&s| s.callsite.name() == "longest_match")
            .next()
            .unwrap();
        let their_search = graph
            .spans()
            .filter(|&s| s.callsite.name() == "alt_longest_match")
            .next()
            .unwrap();
        let rotonda_store_search = graph
            .spans()
            .filter(|&s| s.callsite.name() == "rotonda_store_longest_match")
            .next()
            .unwrap();
        let treebitmap_search = graph
            .spans()
            .filter(|&s| s.callsite.name() == "treebitmap_longest_match")
            .next()
            .unwrap();
        let simple_trie_search = graph
            .spans()
            .filter(|&s| s.callsite.name() == "simple_trie_longest_matching_prefix")
            .next()
            .unwrap();

        // count all tree nodes
        let mut n_nodes = 0;
        let mut n_prefixes = 0;
        let mut n_nodes_by_prefix_len = [0usize; 32];
        let mut n_prefixes_by_prefix_len = [0usize; 32];

        println!("Analysing...");
        tree.visit(&mut |node, depth| {
            n_nodes += 1;

            // The root doesn't represent a valid prefix length, it's just the root of the tree
            if depth > 0 {
                let prefix_len = depth - 1;
                n_nodes_by_prefix_len[prefix_len] += 1;

                if node.has_meta() {
                    n_prefixes += 1;
                    n_prefixes_by_prefix_len[prefix_len] += 1;
                }
            }
        });
        let node_size = std::mem::size_of::<DonkeyTrieNode<()>>();
        let mem_consumed = ((node_size * n_nodes) as f64 / 1024.0).ceil() as i64;
        let mem_consumed_by_prefixes = ((node_size * n_prefixes) as f64 / 1024.0).ceil() as i64;
        let n_prefixes_per_node = (n_prefixes as f64) / (n_nodes as f64);

        println!("Report:");
        println!(
            "  total nodes: {}",
            n_nodes.to_formatted_string(&Locale::en)
        );
        println!(
            "  node size: {} bytes",
            node_size.to_formatted_string(&Locale::en)
        );
        println!(
            "  memory consumption of nodes: {} KiB",
            mem_consumed.to_formatted_string(&Locale::en)
        );
        println!(
            "  total number of prefixes: {}",
            n_prefixes.to_formatted_string(&Locale::en)
        );
        println!(
            "  memory consumption of prefix nodes: {} KiB",
            mem_consumed_by_prefixes.to_formatted_string(&Locale::en)
        );
        println!("  number of prefixes per node: {:.2}", n_prefixes_per_node);

        println!("  tree nodes (N) & prefixes (P) by prefix length (L)");
        println!(
            "    {:>2}: {:-10} [{:-5} ] {:-30} {:-10} [{:-5} ]",
            "L", "#P", "%P", " ", "#N", "%N"
        );
        println!("    {}", "-".repeat(102));
        for i in 1..=32 {
            let cnt_n = n_prefixes_by_prefix_len[i - 1];
            let cnt_p = n_nodes_by_prefix_len[i - 1];
            let pct_n = ((cnt_n as f64) / (n_nodes as f64)) * 100.0;
            let pct_p = ((cnt_p as f64) / (n_nodes as f64)) * 100.0;
            println!(
                "    {:2}: {:10} [{:-5.2}%] {:-30} {:10} [{:-5.2}%] {}",
                i,
                cnt_n.to_formatted_string(&Locale::en),
                pct_n,
                "-".repeat(pct_n.ceil() as usize),
                cnt_p.to_formatted_string(&Locale::en),
                pct_p,
                "#".repeat(pct_p.ceil() as usize)
            );
        }

        println!("Processing statistics:");
        println!("  loading:");
        println!(
            "    loading time : {} milliseconds",
            loading_time.as_millis().to_formatted_string(&Locale::en)
        );
        println!(
            "    parsing time : {} milliseconds",
            parsing_time.as_millis().to_formatted_string(&Locale::en)
        );
        println!(
            "    line count   : {}",
            line_count.to_formatted_string(&Locale::en)
        );
        println!(
            "    record count : {}",
            record_count.to_formatted_string(&Locale::en)
        );
        println!("  insertion:");
        println!(
            "    total count  : {}",
            our_insert.called.to_formatted_string(&Locale::en)
        );
        println!(
            "    total time   : {} milliseconds",
            our_insert
                .elapsed
                .as_millis()
                .to_formatted_string(&Locale::en)
        );
        let mean_insert = our_insert.elapsed.as_secs_f32() / (our_insert.called as f32);
        println!(
            "    mean time    : {} nanoseconds",
            Duration::from_secs_f32(mean_insert)
                .as_nanos()
                .to_formatted_string(&Locale::en)
        );

        let mean_ours = our_search.elapsed.as_secs_f32() / (our_search.called as f32);
        let ops_per_sec_by_mean_ours = (1.0 / mean_ours).floor() as u64;
        println!("  search: (my binary trie)");
        println!(
            "    count        : {}",
            our_search.called.to_formatted_string(&Locale::en)
        );
        println!(
            "    mean time    : {} nanoseconds ({} QPS)",
            Duration::from_secs_f32(mean_ours)
                .as_nanos()
                .to_formatted_string(&Locale::en),
            ops_per_sec_by_mean_ours.to_formatted_string(&Locale::en)
        );

        let mean_theirs = their_search.elapsed.as_secs_f32() / (their_search.called as f32);
        let ops_per_sec_by_mean_theirs = (1.0 / mean_theirs).floor() as u64;
        println!("  search: (ip_network_table crate)");
        println!(
            "    count        : {}",
            their_search.called.to_formatted_string(&Locale::en)
        );
        println!(
            "    mean time    : {} nanoseconds ({} QPS)",
            Duration::from_secs_f32(mean_theirs)
                .as_nanos()
                .to_formatted_string(&Locale::en),
            ops_per_sec_by_mean_theirs.to_formatted_string(&Locale::en)
        );

        let mean_simple_trie =
            simple_trie_search.elapsed.as_secs_f32() / (simple_trie_search.called as f32);
        let ops_per_sec_by_mean_simple_trie = (1.0 / mean_simple_trie).floor() as u64;
        println!("  search: (try-tries-and-trees simple trie)");
        println!(
            "    count        : {}",
            simple_trie_search.called.to_formatted_string(&Locale::en)
        );
        println!(
            "    mean time    : {} nanoseconds ({} QPS)",
            Duration::from_secs_f32(mean_simple_trie)
                .as_nanos()
                .to_formatted_string(&Locale::en),
            ops_per_sec_by_mean_simple_trie.to_formatted_string(&Locale::en)
        );

        let mean_treebitmap =
            treebitmap_search.elapsed.as_secs_f32() / (treebitmap_search.called as f32);
        let ops_per_sec_by_mean_treebitmap = (1.0 / mean_treebitmap).floor() as u64;
        println!("  search: (try-tries-and-trees treebitmap 4,4,4,4,4,4,4,4 strides)");
        println!(
            "    count        : {}",
            treebitmap_search.called.to_formatted_string(&Locale::en)
        );
        println!(
            "    mean time    : {} nanoseconds ({} QPS)",
            Duration::from_secs_f32(mean_treebitmap)
                .as_nanos()
                .to_formatted_string(&Locale::en),
            ops_per_sec_by_mean_treebitmap.to_formatted_string(&Locale::en)
        );

        let mean_rotonda_store =
            rotonda_store_search.elapsed.as_secs_f32() / (rotonda_store_search.called as f32);
        let ops_per_sec_by_mean_rotonda_store = (1.0 / mean_rotonda_store).floor() as u64;
        println!("  search: (rotonda_store::0.2.0 rev 70beea86 TreeBitMap in-memory 4,4,4,4,4,4,4,4 strides)");
        println!(
            "    count        : {}",
            rotonda_store_search.called.to_formatted_string(&Locale::en)
        );
        println!(
            "    mean time    : {} nanoseconds ({} QPS)",
            Duration::from_secs_f32(mean_rotonda_store)
                .as_nanos()
                .to_formatted_string(&Locale::en),
            ops_per_sec_by_mean_rotonda_store.to_formatted_string(&Locale::en)
        );
    }

    #[allow(non_snake_case)]
    fn parse_RISwhois_dump_IPv4_line(line: &str) -> Result<RisWhoisDumpIpv4Item, String> {
        let mut parts = line.split_ascii_whitespace();
        let origin = parts.next();
        let prefix = parts.next();
        let n_ris_peers = parts.next();

        if let (Some(origin), Some(prefix), Some(n_ris_peers)) = (origin, prefix, n_ris_peers) {
            let prefix = Prefix::from_str(prefix)
                .map_err(|err| format!("Invalid prefix '{}': {}", prefix, err))?;
            let origin = origin
                .parse::<u32>()
                .map_err(|err| format!("Invalid origin '{}': {}", origin, err))?;
            let n_ris_peers = n_ris_peers
                .parse::<u16>()
                .map_err(|err| format!("Invalid RIS peer count '{}': {}", n_ris_peers, err))?;

            Ok(RisWhoisDumpIpv4Item {
                origin,
                prefix,
                n_ris_peers,
            })
        } else {
            Err(format!("Line '{}' does not match the expected format: <origin> <tab> <prefix> <tab> <seen by #rispeers>", line))
        }
    }

    #[allow(non_snake_case)]
    fn insert_RISwhois_IPv4_item(
        item: &RisWhoisDumpIpv4Item,
        tree: &mut DonkeyTrie<String>,
    ) -> Result<(), String> {
        if let IpAddr::V4(ipv4) = item.prefix.addr() {
            let bits = u32::from_be_bytes(ipv4.octets());
            tree.push(bits, item.prefix.len()).set_meta(format!(
                "[origin: {}, # ris peers: {}]",
                item.origin, item.n_ris_peers
            ));
            Ok(())
        } else {
            Err(format!("Prefix '{}' is not IPv4", item.prefix))
        }
    }
}
