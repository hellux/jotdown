BEGIN {
    print "use crate::suite_test;"
    print ""
}

$0 ~ "^`{3,}$" {
    l=length($0)
    if (fence == 0) { # enter fence
        print "#[test]"
        fence=l
    } else if (fence == l) { # exit fence
        if (ignore) {
            ignore=0
        } else {
            printf "    let expected = r##\""
            close("src")
            while (getline l < "src") print l
            close("src")
            system("rm -f src")
            print "\"##;"
            print "    suite_test!(src, expected);"
            print "}"
            print ""
        }
        fence=0
    } else {
        print $0 > "src" # md/html
    }
    next
}

fence == 0 && $0 ~ "^`{3,} .*$" {
    ignore=1
    fence=match($0, "[^`]")-1
    next
}

$0 ~ "^\\.$" && !ignore { # enter html
    close("src")
    cmd="cat src | md5sum | cut -c-7"
    cmd | getline hash
    close(cmd)
    printf "fn test_%s() {\n", hash
    printf "    let src = r##\""
    while (getline l < "src") print l
    close("src")
    system("rm -f src")
    print "\"##;"
    next
}

!ignore {
    if (fence) {
        # write to file so content can be piped to md5sum (without having to shell escape)
        print $0 > "src" # md/html
    } else if ($0 != "") {
        printf "// %s\n", $0 # comment
    }
}
