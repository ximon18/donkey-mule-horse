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

        println!("Building tree...");
        for item_result in &data {
            let item = item_result.as_ref().unwrap();
            insert_RISwhois_IPv4_item(item, &mut tree).unwrap();
        }

        let mut table = ip_network_table::IpNetworkTable::new();
        for item_result in &data {
            let prefix = item_result.as_ref().unwrap().prefix;
            let network = ip_network::IpNetwork::new(prefix.addr(), prefix.len()).unwrap();
            let _ = table.insert(network, "foo");
        }

        #[time_graph::instrument]
        fn alt_longest_match<'a, T>(
            table: &'a ip_network_table::IpNetworkTable<T>,
            prefix: &Prefix,
        ) -> (ip_network::IpNetwork, &'a T) {
            table.longest_match(prefix.addr()).unwrap()
        }

        // testing
        println!("Finding longest matching prefixes");
        for item in &data {
            let item = item.as_ref().unwrap();
            let prefix = item.prefix;

            if let (IpAddr::V4(ipv4), len) = prefix.addr_and_len() {
                let bits = u32::from_be_bytes(ipv4.octets());
                let (our_prefix, our_len, _) = tree.longest_match(bits, len).unwrap();
                let our_prefix = Prefix::new_v4(Ipv4Addr::from(our_prefix), our_len).unwrap();
                let (their_prefix, _) = alt_longest_match(&table, &prefix);
                assert_eq!(their_prefix.to_string(), our_prefix.to_string());
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
        println!("  search: (binary tree)");
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
