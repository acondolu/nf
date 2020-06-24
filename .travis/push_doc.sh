#!/bin/bash
set -euxo pipefail

setup_git() {
  git config --global user.email "travis@travis-ci.org"
  git config --global user.name "Travis CI"
}

generate() {
  make coq-doc
}

commit_files() {
  git checkout -b master
  git rm --ignore-unmatch *.html *.css
  cp doc/* .
  git add *.html *.css
  git commit --message "Travis build: $TRAVIS_BUILD_NUMBER"
}

upload_files() {
  git remote add origin-doc https://${GH_TOKEN}@github.com/acondolu/nf.git > /dev/null 2>&1
  git push --quiet --set-upstream origin-doc master
}

setup_git
generate
commit_files
upload_files
