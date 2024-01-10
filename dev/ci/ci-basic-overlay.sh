#!/usr/bin/env bash

# This is the list of repositories used by the CI scripts, unless overridden
# by a call to the "overlay" function in ci-common

declare -a projects # the list of project repos that can be be overlayed

# checks if the given argument is a known project
function is_in_projects {
    for x in "${projects[@]}"; do
      if [ "$1" = "$x" ]; then return 0; fi;
    done
    return 1
}

# project <name> <giturl> <ref> [<archiveurl>]
#   [<archiveurl>] defaults to <giturl>/archive on github.com
#   and <giturl>/-/archive on gitlab
function project {

  local var_ref=${1}_CI_REF
  local var_giturl=${1}_CI_GITURL
  local var_archiveurl=${1}_CI_ARCHIVEURL
  local giturl=$2
  local ref=$3
  local archiveurl=$4
  case $giturl in
    *github.com*) archiveurl=${archiveurl:-$giturl/archive} ;;
    *gitlab*) archiveurl=${archiveurl:-$giturl/-/archive} ;;
  esac

  # register the project in the list of projects
  projects[${#projects[*]}]=$1

  # bash idiom for setting a variable if not already set
  : "${!var_ref:=$ref}"
  : "${!var_giturl:=$giturl}"
  : "${!var_archiveurl:=$archiveurl}"

}

########################################################################
# MathComp
########################################################################
project mathcomp 'https://github.com/math-comp/math-comp' '28837b16a2358f97d31424fc332498a4780c7afe'
# Contact @CohenCyril, @proux01 on github

project mathcomp_1 'https://github.com/math-comp/math-comp' '26c1db2a83deffba627719c3e9b754b2bb83e83b'
# Contact @CohenCyril, @proux01 on github

project fourcolor 'https://github.com/math-comp/fourcolor' '43719c0fb5fb6cb0c8fc1c2db09efc632c23df90'
# Contact @ybertot, @proux01 on github

project oddorder 'https://github.com/math-comp/odd-order' '8dbbae0e53a6d1fcf3471c8fae4dd14c8f18bd93'
# Contact @gares, @proux01 on github

project mczify 'https://github.com/math-comp/mczify' '371b29c7eb30ce408fa29feaf7b94146eed6660b'
# Contact @pi8027 on github

project finmap "https://github.com/math-comp/finmap" "cea9f088c9cddea1173bc2f7c4c7ebda35081b60"
# put back master when Analysis master moves to MathComp 2
# project finmap "https://github.com/math-comp/finmap" "master"
# Contact @CohenCyril on github

project bigenough 'https://github.com/math-comp/bigenough' 'ff71b25f31658d80fdae9657e8cf34e5e1052647'
# Contact @CohenCyril on github

project analysis 'https://github.com/math-comp/analysis' 'b0d400f667f98cedde05414cff99853eb86642b8'
# Contact @affeldt-aist, @CohenCyril on github

########################################################################
# UniMath
########################################################################
project unimath 'https://github.com/UniMath/UniMath' 'ee7af93f47daf41c752e6bd212a7aba78b6a3aaa'
# Contact @benediktahrens, @m-lindgren, @nmvdw, @rmatthes on github

########################################################################
# Unicoq + Mtac2
########################################################################
project unicoq 'https://github.com/unicoq/unicoq' 'e0486d27f687c8c34f530158fee743b3e7a3c259'
# Contact @beta-ziliani, @Janno, @mattam82 on github

project mtac2 'https://github.com/Mtac2/Mtac2' '71640c37a3685db5c7aab069cede807faadacc25'
# Contact @beta-ziliani, @Janno, @mattam82 on github

########################################################################
# Mathclasses + Corn
########################################################################
project math_classes 'https://github.com/coq-community/math-classes' 'f9712ba67b59c90446522e102c87200c7da756ec'
# Contact @spitters on github

project corn 'https://github.com/coq-community/corn' '79e7ee7cc878cd98077d16cfbac12b8133a13805'
# Contact @spitters on github

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris
# and iris_examples repos respectively.
project stdpp "https://gitlab.mpi-sws.org/iris/stdpp" ""
# Contact @RalfJung, @robbertkrebbers on github

project iris "https://gitlab.mpi-sws.org/iris/iris" ""
# Contact @RalfJung, @robbertkrebbers on github

project autosubst 'https://github.com/coq-community/autosubst' '6ba0acccef68c75f6cca8928706c726754d69791'
# Contact @RalfJung, @co-dan on github

project iris_examples 'https://gitlab.mpi-sws.org/iris/examples' '7c5ce0d556f4e03f27ddc6463462bf4040f5103d'
# Contact @RalfJung, @robbertkrebbers on github

########################################################################
# HoTT
########################################################################
project hott 'https://github.com/HoTT/HoTT' '191c10ed39de2fa9821e63b6578f4fba9175ab31'
# Contact @Alizter, @jdchristensen on github

########################################################################
# CoqHammer
########################################################################
project coqhammer 'https://github.com/lukaszcz/coqhammer' '4131a8ccac570336b5ffefd26fd40d879f1e115f'
# Contact @lukaszcz on github

########################################################################
# Flocq
########################################################################
project flocq 'https://gitlab.inria.fr/flocq/flocq' '3e8b2e09d79ce3c150a732dd446610d63dabc759'
# Contact @silene on github

########################################################################
# coq-performance-tests
########################################################################
project coq_performance_tests 'https://github.com/coq-community/coq-performance-tests' 'c5e2f8d0b0057a003dcaec727ba01f38e519bf6d'
# Contact @JasonGross on github

########################################################################
# coq-tools
########################################################################
project coq_tools 'https://github.com/JasonGross/coq-tools' '32dcc6b48607c34442e64789eaaf894dac3dd020'
# Contact @JasonGross on github

########################################################################
# Coquelicot
########################################################################
project coquelicot 'https://gitlab.inria.fr/coquelicot/coquelicot' '218b5cca041712775999f3c5ab0cac2f99defb7f'
# Contact @silene on github

########################################################################
# CompCert
########################################################################
project compcert 'https://github.com/AbsInt/CompCert' 'c7b27e30a9057c14d5a02a9f9aa3d8f230715eb0'
# Contact @xavierleroy on github

########################################################################
# VST
########################################################################
project vst 'https://github.com/PrincetonUniversity/VST' '6d2eb96dd42a4d3ee398eef8224e6a8ccca5c750'
# Contact @andrew-appel on github

########################################################################
# cross-crypto
########################################################################
project cross_crypto 'https://github.com/mit-plv/cross-crypto' 'c46bbe27ef7a05a82f744230c6f2d5f1fdefdaaa'
# Contact @andres-erbsen on github

########################################################################
# rewriter
########################################################################
project rewriter 'https://github.com/mit-plv/rewriter' '026f87bfbc5d235c3f7f31b24199305d616daff3'
# Contact @JasonGross on github

########################################################################
# fiat_parsers
########################################################################
project fiat_parsers 'https://github.com/mit-plv/fiat' '157f13408ef9731ccf0829fbcac3c11b9856fb81'
# Contact @JasonGross on github

########################################################################
# fiat_crypto
########################################################################
project fiat_crypto 'https://github.com/mit-plv/fiat-crypto' '4d9fadc163b8a09d75a6836e08f52f051fa489d4'
# Contact @andres-erbsen, @JasonGross on github

########################################################################
# fiat_crypto_legacy
########################################################################
project fiat_crypto_legacy 'https://github.com/mit-plv/fiat-crypto' '47058dc312a5cad924972056cdfc4de06c432a82'
# Contact @JasonGross on github

########################################################################
# coq_dpdgraph
########################################################################
project coq_dpdgraph 'https://github.com/coq-community/coq-dpdgraph' '8452ebdebb34f66c0b87b39b757784090772fd49'
# Contact @Karmaki, @ybertot on github

########################################################################
# CoLoR
########################################################################
project color 'https://github.com/fblanqui/color' '42f4b271d41b81d59508936a375ac2f9fafe6b9c'
# Contact @fblanqui on github

########################################################################
# TLC
########################################################################
project tlc 'https://github.com/charguer/tlc' '1f1df8cfbdfb1838a446fa1614c8572486c0478f'
# Contact @charguer on github

########################################################################
# Bignums
########################################################################
project bignums 'https://github.com/coq/bignums' 'cb65c878e764793081ead5fdcaffbe018dd713c3'
# Contact @erikmd, @proux01 on github

########################################################################
# coqprime
########################################################################
project coqprime 'https://github.com/thery/coqprime' 'd5935ca3b7f3d2f738b0810a49858d17480d6a58'
# Contact @thery on github

########################################################################
# bbv
########################################################################
project bbv 'https://github.com/mit-plv/bbv' 'f4caa0504125460afa41fb92c9071dd628154d8b'
# Contact @JasonGross, @samuelgruetter on github

########################################################################
# bedrock2
########################################################################
project bedrock2 'https://github.com/mit-plv/bedrock2' '65988d2662e522b0a7dcd04ce66c47acb5c66df1'
# Contact @samuelgruetter, @andres-erbsen on github

########################################################################
# Coinduction
########################################################################
project coinduction 'https://github.com/damien-pous/coinduction' '65d020794e817fcf0295566abe1be454ad3284e4'
# Contact @damien-pous on github

########################################################################
# coq-lsp
########################################################################
project coq_lsp 'https://github.com/ejgallego/coq-lsp' '75a92e0abeb29cbc3f75bbffa60db04857789070'
# Contact @ejgallego on github

########################################################################
# Equations
########################################################################
project equations 'https://github.com/mattam82/Coq-Equations' 'a517a3e128719b078397a415dc9ce6b856019245'
# Contact @mattam82 on github

########################################################################
# Elpi + Hierarchy Builder
########################################################################
project elpi 'https://github.com/LPCIC/coq-elpi' 'b753aa43a643ad7c0b2722d9850253b9d737fec7'
# Contact @gares on github

project hierarchy_builder 'https://github.com/math-comp/hierarchy-builder' 'b4e8cbce83cff0f817494adc625a127bd4114b2e'
# Contact @CohenCyril, @gares on github

########################################################################
# Engine-Bench
########################################################################
project engine_bench 'https://github.com/mit-plv/engine-bench' '8c0b15abc38b1d3f7dc606f4eeef9fba1a986b05'
# Contact @JasonGross on github

########################################################################
# fcsl-pcm
########################################################################
project fcsl_pcm 'https://github.com/imdea-software/fcsl-pcm' '35cb0a2235adb656c2696e33512f0c4555ad753b'
# Contact @aleksnanevski, @clayrat on github

########################################################################
# ext-lib
########################################################################
project ext_lib 'https://github.com/coq-community/coq-ext-lib' '00d3f4e2a260c7c23d2c0b9cbc69516f8be4ac92'
# Contact @gmalecha, @liyishuai on github

########################################################################
# simple-io
########################################################################
project simple_io 'https://github.com/Lysxia/coq-simple-io' '7b1e6de2c2028a35776f080dc3db117cae117836'
# Contact @Lysxia, @liyishuai on github

########################################################################
# quickchick
########################################################################
project quickchick 'https://github.com/QuickChick/QuickChick' '7c570ed650f770e29ea6a84d49687b1c0c2b6b72'
# Contact @lemonidas, @Lysxia, @liyishuai on github

########################################################################
# reduction-effects
########################################################################
project reduction_effects 'https://github.com/coq-community/reduction-effects' 'f0570f498bc8a0d25e878115b4066b140908c4b4'
# Contact @liyishuai, @JasonGross on github

########################################################################
# menhirlib
########################################################################
# Note: menhirlib is now in subfolder coq-menhirlib of menhir
project menhirlib 'https://gitlab.inria.fr/fpottier/menhir' 'bb68b8fdb186266dbed67599cfa69a69a3c01272'
# Contact @fpottier, @jhjourdan on github

########################################################################
# coq-neural-net-interp
########################################################################
project neural_net_interp 'https://github.com/JasonGross/neural-net-coq-interp' '06509a99be412d06847de938a19e02be64f6fc4c'
# Contact @JasonGross on github

########################################################################
# aac_tactics
########################################################################
project aac_tactics 'https://github.com/coq-community/aac-tactics' '059dd94f4fbfe23e93d5c3de800cfb71f6a0ed43'
# Contact @palmskog on github

########################################################################
# paco
########################################################################
project paco 'https://github.com/snu-sf/paco' '5c5693f46c8957f36a2349a0d906e911366136de'
# Contact @minkiminki on github

########################################################################
# coq-itree
########################################################################
project itree 'https://github.com/DeepSpec/InteractionTrees' 'dda104937d79e2052d1a26f6cbe89429245ff743'
# Contact @Lysxia on github

########################################################################
# coq-itree_io
########################################################################
project itree_io 'https://github.com/Lysxia/coq-itree-io' 'af0326793a19f142eba800dba6044143b108ceaa'
# Contact @Lysxia, @liyishuai on github

########################################################################
# coq-ceres
########################################################################
project ceres 'https://github.com/Lysxia/coq-ceres' 'f61b24d48222db0100de19f88c19151a3aeb826f'
# Contact @Lysxia on github

########################################################################
# coq-parsec
########################################################################
project parsec 'https://github.com/liyishuai/coq-parsec' '2efb4437f8451dfbeb174368f860e629135c08ab'
# Contact @liyishuai on github

########################################################################
# coq-json
########################################################################
project json 'https://github.com/liyishuai/coq-json' '2d1d11eb1be9ad96614d9cd224c1df7c75ec2869'
# Contact @liyishuai on github

########################################################################
# coq-async-test
########################################################################
project async_test 'https://github.com/liyishuai/coq-async-test' '0637b95ae52060d8a808261ca97890d03c9a4503'
# Contact @liyishuai on github

########################################################################
# coq-http
########################################################################
project http 'https://github.com/liyishuai/coq-http' 'cabde79a4a0d978d031475c7443be7fd43a711c5'
# Contact @liyishuai on github

########################################################################
# paramcoq
########################################################################
project paramcoq 'https://github.com/coq-community/paramcoq' 'a61b1b3f8cea3fce6c904a0b8da6236345ed896f'
# Contact @proux01 on github

########################################################################
# relation_algebra
########################################################################
project relation_algebra 'https://github.com/damien-pous/relation-algebra' '38cfe670448c90406fb72ff40526ad4d08b75319'
# Contact @damien-pous on github

########################################################################
# StructTact + InfSeqExt + Cheerios + Verdi + Verdi Raft
########################################################################
project struct_tact 'https://github.com/uwplse/StructTact' '97268e11564c8fe59aa72b062478458d7aa53e9d'
# Contact @palmskog on github

project inf_seq_ext 'https://github.com/DistributedComponents/InfSeqExt' '601e89ec019501c48c27fcfc14b9a3c70456e408'
# Contact @palmskog on github

project cheerios 'https://github.com/uwplse/cheerios' '5c9318c269f9cae1c1c6583a44405969ac0be0dd'
# Contact @palmskog on github

project verdi 'https://github.com/uwplse/verdi' 'f082f86b2a0cb56cc0703a79da351d8b9a6e7468'
# Contact @palmskog on github

project verdi_raft 'https://github.com/uwplse/verdi-raft' 'a3375e867326a82225e724cc1a7b4758b029376f'
# Contact @palmskog on github

########################################################################
# stdlib2
########################################################################
project stdlib2 'https://github.com/coq/stdlib2' '33212e05c51efa012c9dfccd0b9e735a42f2d924'
# Contact @maximedenes, @vbgl on github

########################################################################
# argosy
########################################################################
project argosy 'https://github.com/mit-pdos/argosy' 'a6a5aa0d3868efd4ada0b40927b5748e5d8967d3'
# Contact @tchajed on github

########################################################################
# ATBR
########################################################################
project atbr 'https://github.com/coq-community/atbr' '39de8e4c654a530238390704677a672275649d12'
# Contact @palmskog, @tchajed on github

########################################################################
# perennial
########################################################################
project perennial 'https://github.com/mit-pdos/perennial' 'd045aca7d0bd3c43ec561179954777f160eed1e4'
# Contact @upamanyus, @RalfJung, @tchajed on github
# PRs to fix Perennial failures should be submitted against the Perennial
# `master` branch. `coq/tested` is automatically updated every night to the
# `master` branch if CI on `master` is green. This is to avoid breaking Coq CI
# when Perennial CI breaks.

########################################################################
# metacoq
########################################################################
project metacoq 'https://github.com/MetaCoq/metacoq' '194116d4f80dc53253f8730aa822c52225731d71'
# Contact @mattam82, @yforster on github

########################################################################
# SF suite
########################################################################
project sf 'https://github.com/DeepSpec/sf' 'd7f9ab78cd01f36ce5a2a359dfe4cfe1e160fae9'
# Contact @bcpierce00, @liyishuai on github

########################################################################
# Coqtail
########################################################################
project coqtail "https://github.com/whonore/Coqtail" "ecca5017b6b27e1bded009f9725186d941d85b53"
# Contact @whonore on github

########################################################################
# Deriving
########################################################################
project deriving 'https://github.com/arthuraa/deriving' '9d6aea3df446854aa1aa009e50954e2fd0c02981'
# Contact @arthuraa on github

########################################################################
# VsCoq
########################################################################
project vscoq 'https://github.com/coq-community/vscoq' '84032c7f46e0a21a01da91e5364cfc7d4951e297'
# Contact @rtetley, @gares on github

########################################################################
# category-theory
########################################################################
project category_theory 'https://github.com/jwiegley/category-theory' '41ab38d0caffaa5176a6f63810ba8d92816514a4'
# Contact @jwiegley on github

########################################################################
# itauto
########################################################################
project itauto 'https://gitlab.inria.fr/fbesson/itauto' 'a527a27d9dd21ac8f69821f35fd677314d5eadbe'
# Contact @fajb on github

########################################################################
# Mathcomp-word
########################################################################
project mathcomp_word "https://github.com/jasmin-lang/coqword" "537141ac0dbdd0a0ca2b409826d93a6f8398b0b3"
# Contact @vbgl, @strub on github
# go back to "main" and change dependency to MC 2 when
# https://github.com/jasmin-lang/jasmin/pull/560 is merged

########################################################################
# Jasmin
########################################################################
project jasmin 'https://github.com/jasmin-lang/jasmin' 'd195c58958771ba26bc479fef9a5f04fd219290e'
# Contact @vbgl, @bgregoir on github

########################################################################
# Lean Importer
########################################################################
project lean_importer 'https://github.com/SkySkimmer/coq-lean-import' '10363695d2f9692b4d8a9e7ee29be444ebe96c80'
# Contact @SkySkimmer on github

########################################################################
# SerAPI
########################################################################
project serapi 'https://github.com/ejgallego/coq-serapi' 'ba0bd1d3fb086b7a7c79adc68d1aa53e9d883d42'
# Contact @ejgallego on github

########################################################################
# SMTCoq
########################################################################
project smtcoq 'https://github.com/smtcoq/smtcoq' 'e24b14768d6f61c915bc25734d769bbe9f044775'
# Contact @ckeller on github

########################################################################
# Stalmarck
########################################################################
project stalmarck 'https://github.com/coq-community/stalmarck' '22a05ddcc6a826ffa772282f1d3a0902d3921e7b'
# Contact @palmskog on github

########################################################################
# coq-library-undecidability
########################################################################
project coq_library_undecidability 'https://github.com/uds-psl/coq-library-undecidability' '91165e2e95d4372d692aca05f5d53ab628e3c8b9'
# Contact @mrhaandi, @yforster on github

########################################################################
# Tactician
########################################################################
project tactician 'https://github.com/coq-tactician/coq-tactician' '938ee07cba9719753f7f975addc611cd115f3504'
# Contact @LasseBlaauwbroek on github

########################################################################
# Ltac2 compiler
########################################################################
project ltac2_compiler 'https://github.com/SkySkimmer/coq-ltac2-compiler' '9fd8b13fd2eb9b3ed49e76e944c5e2f211d7c52d'
# Contact @SkySkimmer on github

########################################################################
# Waterproof
########################################################################
project waterproof 'https://github.com/impermeable/coq-waterproof' 'aec4fbe2a9b586b246e18b00a52c66ee7a772e79'
# Contact @jellooo038, @jim-portegies on github
