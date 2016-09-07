# agda-travis
Example repo for building Agda files with Travis CI.

[![Build Status](https://travis-ci.org/scott-fleischman/agda-travis.svg?branch=master)](https://travis-ci.org/scott-fleischman/agda-travis)

Note that the Travis CI config builds Agda using [`stack`](https://docs.haskellstack.org/) as part of the `before_install` section. This can take 20-30 minutes for the first build. Subsequent builds will use the build cache and will not need to build Agda again.
