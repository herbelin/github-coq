#!/bin/sh

if [ "$CI_PULL_REQUEST" = "7257" ] || [ "$CI_BRANCH" = "master+fix-yet-another-unif-dep-in-alphabet" ]; then
    UniMath_CI_BRANCH=master+fix-PR7257+sensitivity-unif-variable-name
    UniMath_CI_GITURL=https://github.com/herbelin/UniMath.git
fi
