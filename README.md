This repository contains some very rough experimentation with Rust implementations of IP address lookup algorithms, both my own and comparison with those of others.

This is just a learning playground for myself, it is not intended to be used in deployed applications.

The repository is named after the https://blog.nlnetlabs.nl/donkeys-mules-horses/ article.

For the `donkey_binary_trie_with_RISwhois_IPv4_data_full` test download and unzip a RIS WHOIS dump file first with:

```
$ curl -JLO https://www.ris.ripe.net/dumps/riswhoisdump.IPv4.gz
$ gunzip riswhoisdump.IPv4.gz
```