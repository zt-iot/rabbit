rm -f examples/_camserver.rab.spthy

if ! dune exec bin/rabbit.exe -- examples/camserver.rab -o tamarin_models/camserver_tt_pp.spthy --post-process --tag-transition > /dev/null 2>&1; then
    exit 2
fi

if diff tamarin_models/reference_camserver_tt_pp.spthy tamarin_models/camserver_tt_pp.spthy; then
    echo pass
else
    echo DIFF FOUND
    exit 2
fi

# tamarin-prover camserver.rab.spthy --prove=
