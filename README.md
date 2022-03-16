# chain-replication

TLA+ for [Percolator](https://research.google/pubs/pub36726/).

```bash
# Check
java -XX:+UseParallelGC -Xmx12g -cp tla2tools.jar tlc2.TLC -workers auto spec.tla
```

This TLA+ model is of the percolator algorithm for implementing multi-row atomic transactions on top of a single-row atomic transaction system. See my [blog post](https://danwt.github.io/concurrent_algorithms/2022/03/05/0.html).

The failure model is crash stop or crash recover.
