RAB=$1
MODULE=$(echo $RAB | sed -e 's/\.rab$//')

echo MODULE $MODULE

rm -f _$MODULE.spthy $MODULE.log

if ! dune exec ../src/rabbit.exe -- $MODULE.rab -o _$MODULE.spthy --post-process --tag-transition > $MODULE.log 2>&1 ; then
    cat $MODULE.log
    exit 2
fi

if [ -f $MODULE.spthy ]; then
    if diff $MODULE.spthy _$MODULE.spthy; then
	echo pass
    else
	echo _$MODULE.spthy is different from $MODULE.spthy
	exit 2
    fi
else
    cp _$MODULE.spthy $MODULE.spthy
fi

tamarin-prover $MODULE.spthy --prove= >> $MODULE.log 2>&1 
tail -20 $MODULE.log
