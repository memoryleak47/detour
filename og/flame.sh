RUSTFLAGS="-C force-frame-pointers=yes" cargo flamegraph
firefox flamegraph.svg
