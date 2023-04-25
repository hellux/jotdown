c_awk_latest='
/^## \[.*\]/ {if (latest) exit; else {latest=1; next}}
latest {print}
'

tag=$(grep ^version Cargo.toml | cut -d" " -f3 | tr -d '"')
changes=$(awk "$c_awk_latest" CHANGELOG.md | tail -n+2)

git -c core.commentchar='%' tag --edit \
    -m "Release $tag" \
    -m "$changes" \
    "$tag"
git push github master "$tag"
