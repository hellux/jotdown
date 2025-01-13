# run one or more benchmarks, for use together with bench_table.sh
# usage: ./bench_row.sh [-i] [-c crit_bench]..

{
    git log --oneline | head -n1

    while getopts i:c: flag; do
        case "$flag" in
            c)
                # try to reduce noise by selecting max throughput of multiple runs
                for _ in $(seq 100); do
                    cargo bench -p bench-crit -- --quick "$OPTARG" 2>|/dev/null \
                        | awk 'NR == 2 {print $4}'
                done | sort -rV | head -n1
                ;;
            *)
                exit 1
                ;;
        esac
    done
} | tr "\n" "\t"

echo
