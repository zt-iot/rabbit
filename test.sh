rm -f examples/_camserver.rab.spthy

if ! dune exec src/rabbit.exe -- examples/camserver.rab -o examples/_camserver.rab.spthy --post-process --tag-transition > /dev/null 2>&1; then
    exit 2
fi

if diff examples/camserver.rab.spthy examples/_camserver.rab.spthy; then
    echo pass
else
    echo DIFF FOUND
    exit 2
fi

# tamarin-prover camserver.rab.spthy --prove=
