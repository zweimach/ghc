# Contributing to GHC

First, thanks for your interest in contributing to GHC! Contributors like you
are the reason why GHC continues to evolve and improve.

GHC is a large project and there are many ways that you can contribute.
These include

 * [Submitting bug reports](#submitting-bug-reports)
 * [Triaging tickets](#triaging-tickets)
 * [Improving documentation](#improving-documentation)
 * [Writing patches](#writing-patches)
 * [Reviewing patches](#reviewing-patches)

Let's look at each of these in more detail.

## Submitting bug reports

Like all software, GHC has quirks, bugs, and missing features. If you encounter
any of these we would love to hear about it. Even if you are unsure of whether
what you see is a bug feel free to submit a bug report
via [Trac](https://ghc.haskell.org/trac/ghc/newticket). Be sure to include any
relevant specifics of your environment. Also, provide a code example if you have
one: a bit of code is worth a thousand words. For an example of an exemplary
bug report see, for
instance, [#11126](https://ghc.haskell.org/trac/ghc/ticket/11126).

## Triaging tickets

Staying on top of GHC's issue tracker requires a significant amount of effort;
any help you can provide in sorting, characterising, and closing old bugs is
greatly appreciated. GHC uses [Trac](https://ghc.haskell.org/trac/ghc) for issue
tracking. Trac allows us to record a variety of metadata about each bug,
including

 * `Type`: Is the ticket a bug or feature request?
 * `Status`: The state of the ticket. This takes the following values, listed in
   typical chronological order,
    1. `New`: The state a ticket starts in; the ticket is waiting for someone to
       look at it and/or discussion is underway on how to fix the issue.
    2. `Assigned`: Someone has said they are working on the issue
    3. `Patch`: There is a patch (typically listed in the `Differential Rev(s)`
       field) fixing the issue waiting for review.
    4. `Merge`: A fix has been committed to the `master` branch and we are
       considering backporting it to the stable branch.
    5. `Closed`: As of the release listed in the `Milestone` field the issue is
       considered to be resolved.
 * `Priority`: How likely is the issue to break user applications? How bad is
   the breakage? Segmentation faults and data corruption are generally
   considered to be `highest` priority. For everything else, use your judgement.
 * `Version`: The earliest GHC release the issue was observed in.
 * `Milestone`: When was/will the issue be fixed. Specifically the first GHC
   release which the issue will not affect.
 * `Component`: What part of the project is the issue applicable to? e.g. the
   typechecker, code generator, core libraries, or parser.
 * `Differential Rev(s)`: Lists Phabricator [Differentials](#writing-patches)
   relevant to the issue.

Triaging a bug usually involves the following,

 * Determine whether the ticket is complete. Are important details missing? Does
   it include a reproduction case?
 * Has a testcase been added to GHC's testsuite? If not feel free to
   [add one](https://ghc.haskell.org/trac/ghc/wiki/Building/RunningTests/Adding)
   (marking it as `expect_broken` if appropriate). See
   the [writing patches](#writing-patches) section below for details on
   submitting patches.
 * Is the ticket still applicable? Try reproducing the bug in the latest GHC
   release (and the `master` branch, if you are able). If it's still broken then
   leave a comment saying so. If not feel free to close it, updating the
   `Milestone` field with the GHC release that you tested with.
 * Are the `Type`, `Priority`, and `Version` fields set appropriately? Feel free
   to update them if you think not.
 * Do you think you can fix the issue? If so, great! See
   [writing patches](#writing-patches) to get started with your patch.

## Improving documentation

GHC and its core libraries have a very large surface area, all of which needs to
have explanatory user documentation. This documentation falls into a few
categories,

 * the GHC users guide (see `docs/users_guide`). Some documentation for editing
   the users guide can be found in
   the [GHC Wiki](https://ghc.haskell.org/trac/ghc/wiki/Commentary/UserManual).
 * core library documentation (see the Haddocks in `libraries/base`,
   `libraries/ghc-prim`, etc.)
 * implementation documentation in the source code (search for `Note` in
   `compiler/`)

Improving this documentation can have an enormous impact on GHC's users. We are
happy to accept [GitHub pull requests](https://github.com/ghc/ghc/pulls) for
this sort of contribution.

## Writing patches

Do you have a feature that you would like to see implemented or bug that needs
fixing? Working on GHC can be fun and rewarding. Don't worry if you aren't yet
familiar with GHC's internals, there are plenty of resources to learn from,
including

 * the lengthy `Note`s scattered through GHC's source code (search for `Note`)
 * the many [papers](https://ghc.haskell.org/trac/ghc/wiki/ReadingList) that
   have been written about GHC
 * the [commentary](https://ghc.haskell.org/trac/ghc/wiki/Commentary) articles
   in the GHC Wiki
 * [help](#getting-help) from other helpful GHC developers

The easiest way to start working within GHC is generally to fix a bug. In
particular, we keep
a [list](https://ghc.haskell.org/trac/ghc/wiki/Newcomers#Findingaticket) of
tickets which we think might be appropriate for a new-comer. Choose one that
looks interesting and give it a shot. Don't hesitate to ask for help if you get
stuck.

See the
[Quick Start guide](https://ghc.haskell.org/trac/ghc/wiki/Building/QuickStart)
for instructions on building your tree. If you encounter trouble, just don't
hesitate to [ask for help](#getting-help). Once your have a patch there are
two ways to submit it for review,

 * for trivial changes (a few lines of relative uncontroversial changes) we will
   accept changes via a [GitHub pull request](https://github.com/ghc/ghc/pulls).
 * for all other changes we use [Phabricator](https://phabricator.haskell.org/).
   See the [Phabricator guide](https://ghc.haskell.org/trac/ghc/wiki/Phabricator)
   for details on how to submit your patch for review. For an example of an
   exemplary patch see, for
   instance, [D3542](https://phabricator.haskell.org/D3542).

### User-visible changes and language extensions

Once you have a few bugs under your belt, you might consider moving on to
more complex features. GHC has
a [proposal process](https://github.com/ghc-proposals/ghc-proposals) for
discussing and refining user-visible changes to the language and high-impact
compiler changes. If you have an idea for such a change, write up a proposal and
see what others think.

## Reviewing patches

Code review is crucial to keeping GHC a maintainable, reliable piece of
software. Unfortunately, reviewers are always in short supply. If you have some
knowledge of GHC's internals do swing
by [Phabricator](https://phabricator.haskell.org/differential/), choose a
Differential, and provide your feedback.

When reviewing try to not get too bogged down in typographical errors and style;
the most valuable reviews are those which shed new light on a problem, reveal
potential bugs in an implementation, or suggest a cleaner way to factor an idea.
That isn't to say that stylistic concerns shouldn't be discussed; we merely want
to avoid that these issues are the primary focus of discussion.


## Getting help

If you are lost, get stuck, or need to talk something through, don't hesitate to
reach out. GHC developers are almost always available via IRC in the `#ghc`
channel on `irc.freenode.net`. You can also get help via the `ghc-devs`
[mailing list](https://www.haskell.org/mailman/listinfo/ghc-devs).

## Other resources

In addition to the resources listed above, Takenobu Tani has written a set of
great documents summarizing
GHC's
[development process](https://takenobu-hs.github.io/downloads/ghc_development_flow.pdf)
and
[implementation](https://takenobu-hs.github.io/downloads/haskell_ghc_illustrated.pdf).
Also, the [Newcomers page] on the GHC Wiki covers many of the same issues
discussed here in greater depth.
