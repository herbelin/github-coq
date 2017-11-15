if [ "$TRAVIS_PULL_REQUEST" = "6134" ] || [ "$TRAVIS_BRANCH" = "master+type-scope-cast" ]; then
    mathcomp_CI_BRANCH=master+cast-notation-rule
    mathcomp_CI_GITURL=https://github.com/herbelin/math-comp.git
    math_classes_CI_BRANCH=master+adapting-cast-using-scope-bound-to-type
    math_classes_CI_GITURL=https://github.com/herbelin/math-classes.git
    HoTT_CI_BRANCH=master+adapting-cast-using-scope-bound-to-type
    HoTT_CI_GITHUB=https://github.com/herbelin/HoTT.git
fi
