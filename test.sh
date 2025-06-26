rm -f examples/_camserver.spthy

if ! dune exec src/rabbit.exe -- examples/camserver.rab -o examples/_camserver.spthy --post-process --tag-transition > /dev/null 2>&1; then
    exit 2
fi

if diff -c examples/camserver.spthy examples/_camserver.spthy; then
    echo pass
else
    echo DIFF FOUND
    exit 2
fi

if ! dune exec src/rabbit.exe -- examples/camserver_param.rab -o examples/_camserver_param.spthy --post-process --tag-transition > /dev/null 2>&1; then
    exit 2
fi

if diff -c examples/camserver_param.spthy examples/_camserver_param.spthy; then
    echo pass
else
    echo DIFF FOUND
    exit 2
fi

# tamarin-prover camserver.rab.spthy --prove=
