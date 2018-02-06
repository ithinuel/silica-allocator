#!/bin/bash
PKGID="$(cargo pkgid)"
[ -z "$PKGID" ] && exit 1
ORIGIN="${PKGID%#*}"

PKGNAMEVER="${PKGID#*#}"

if [[ $PKGNAMEVER == *":"* ]]; then
    PKGNAME="${PKGNAMEVER%:*}"
else
    PKGNAME="${ORIGIN##*/}"
fi
BINNAME="${PKGNAME/-/_}"
ORIGIN="${ORIGIN:7}"
shift

cargo test --no-run || exit $?

shopt -s extglob
EXE=($ORIGIN/target/debug/$BINNAME-!(*.d))
shopt -u extglob

echo ${#EXE[*]} ${EXE[*]}

if [ ${#EXE[*]} -ne 1 ]; then
    echo 'Non-unique test file, retrying...' >2
    rm -f ${EXE[*]}
    cargo test --no-run || exit $?
fi

rm -rf $ORIGIN/target/cov
kcov --exclude-pattern=/.cargo,/usr/lib --verify $ORIGIN/target/cov ${EXE[0]}

