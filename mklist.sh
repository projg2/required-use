#! /bin/sh

for i in $(<$1); do
        v="$(portageq metadata / ebuild ${i} REQUIRED_USE)"
        [ -n "$v" ] && echo "$i $v"
done
