#!/bin/sh

cmd=$*

test_html=$(echo "abc" | $cmd | tr -d ' \n')
[ "$test_html" != "<p>abc</p>" ] && echo "failed simple gen: '$test_html'" && exit 1

for f in *.dj; do
    tmp=$(mktemp)
    for i in $(seq 500); do
        cat "$f" >> $tmp
    done
    t=$(cat "$tmp" \
        | (LANG=C time -p $cmd > /dev/null) 2>&1 \
        | grep real \
        | awk '{print $2}')
    printf "$t\t$f\n"
    rm -f "$tmp"
done | sort -rn
