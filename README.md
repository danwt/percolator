# percolator

TLA+ for [Percolator](https://research.google/pubs/pub36726/).

```bash
# Check
java -XX:+UseParallelGC -Xmx12g -cp tla2tools.jar tlc2.TLC -workers auto spec.tla
```

This TLA+ model is of the percolator algorithm for implementing multi-row atomic transactions on top of a single-row atomic transaction system. See my [blog post](https://danwt.github.io/256107470762584521452889353055328985483).

The failure model is crash stop or crash recover.
