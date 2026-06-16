#!/bin/sh

mkdir public
cp -r copy/* public
sed -f variables.sed install.prehtml > public/install.html
cat publisheader.html publis.html publisfooter.html > public/publications.html
