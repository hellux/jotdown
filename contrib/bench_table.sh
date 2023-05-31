# run benchmarks over a range of commits and assemble a table
# usage: ./contrib/bench_table.sh [-r RANGE] -- BENCHMARKS

range="master.."
while getopts r: flag; do
    case "$flag" in
        r) range=$OPTARG;;
        *) exit 1;;
    esac
done
shift $((OPTIND-1))

[ -z "$*" ] && exit 1

make bench || exit 1

current="$(git rev-parse --abbrev-ref HEAD)"

trap "git checkout $current" EXIT

< /proc/cpuinfo grep "model name" | head -n1
{
    {
        echo "commit"
        OPTIND=1
        while getopts i:c: flag "$@"; do
            case "$flag" in
                i) echo "iai:$OPTARG [cycles]";;
                c) echo "criterion:$OPTARG [MB/s]";;
                *) exit 1
            esac
        done
    } | tr "\n" "\t"
    echo
    set -x
    for commit in $(git rev-list --reverse --topo-order "$range"); do
        git checkout "$commit" >/dev/null
        ./contrib/bench_row.sh "$@" | tee /proc/self/fd/2
    done
} | column -t -s"$(printf "\t")"
