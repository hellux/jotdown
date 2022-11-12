BEGIN {
    print "use crate::suite_test;"
    print ""
}

$0 ~ "^`{3,}$" {
    l=length($0)
    if (fence == 0) { # enter fence
        print "#[test]"
        printf "fn test%02d() {\n", count
        printf "    let src = r##\""
        fence=l
        count+=1
    } else if (fence == l) { # exit fence
        if (ignore) {
            ignore=0
        } else {
            print "\"##;"
            print "    suite_test!(src, expected);"
            print "}"
            print ""
        }
        fence=0
    } else {
        print $0 # md/html
    }
    next
}

fence == 0 && $0 ~ "^`{3,} .*$" {
    ignore=1
    fence=match($0, "[^`]")-1
    next
}

$0 ~ "^\\.$" && !ignore { # enter html
    print "\"##;"
    printf "    let expected = r##\""
    next
}

!ignore {
    if (fence==0 && $0 != "") { # comment
        printf "// "
    }
    print $0 # comment/md/html
}
