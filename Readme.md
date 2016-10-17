#Interative Hybrid Probabilistic Model Counting

[Interative Hybrid Probabilistic Model Counting (IHPMC)](http://www.steffen-michels.de/ihpmc/) is a probabilistic inference algorithm developed at the [Institute for Computing and Information Sciences](http://www.ru.nl/icis/) of the [Radboud University Nijmegen](http://www.ru.nl/) by Steffen Michels. The algorithm offers inference for hybrid models with bounded error. This is a unique selling point compared to other methods, for example based on sampling, which do, if at all, only provide weak guarantees on the error. This is achieved by iteratively evaluating a hybrid probability tree and computing bounds on probabilities. Details can be found in the publication:

Steffen Michels, Arjen Hommersom, Peter J. F. Lucas <br />
[Approximate Probabilistic Inference with Bounded Error for Hybrid Probabilistic Logic Programming](http://www.steffen-michels.de/articles/ijcai16.pdf)


The input language is similar to [Probabilistic Constraint Logic Programming (PCLP)](http://www.steffen-michels.de/pclp), but does only support precise distributions.


##Installation

The inference tool based on IHPMC is written in Haskell and there is a Cabal package file. You can install the package with:

    cabal install

There are also binary x64 Linux executables in a [downloadable package](http://www.steffen-michels.de/ihpmc/ihpmc_linux_x64.tar.gz) (which may be outdated).

##Usage

The algorithm comes with two version "ihpmc_float" and "ihpmc_exact". The former uses floating point arithmetic and the latter exact rational number arithmetic to compute probabilities. Floating point arithmetic is usually the better choice. It is more efficient, but can result in rounding errors. However, those rounding errors usually only become problematic, when conditioning on events with very small probability. Note, that even when using "ihpmc_exact" rounding error occur when computing CDF values for continuous distributions.

The models used for the experiments of the paper "Approximate Probabilistic Inference with Bounded Error for Hybrid Probabilistic Logic Programming" are included in "examples". You can run one of the models for instance with (after installing with Cabal):

    ihpmc_float examples/diagnostic_10_01_30.pclp -i 10000

or, in case you use the binary package:

    bin/ihpmc_float examples/diagnostic_10_01_30.pclp -i 10000

This will compute the result for 10000 iterations. The expected output is:

    Stopping after 10000 iterations.
    iteration 10000: 0.3884685469174709 (error bound: 0.08105175979731041)

Instead of the number of iterations, it is also possible to specify a timeout (-t) or a maximal allowed error (-e) as stop condition. The conditions can also be combined. For instance, with the following options inference will stop after 2000 iterations, after 1000ms or if the maximal error of the approximation is at most 0.01 (whatever occurs first):

    ihpmc_float examples/diagnostic_10_01_30.pclp -i 2000 -t 1000 -e 0.01

