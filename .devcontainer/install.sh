#!/bin/bash -i

## Fix issues with gitpod's stock .bashrc
cp /etc/skel/.bashrc $HOME

## Shorthands for git
git config --global alias.slog 'log --pretty=oneline --abbrev-commit'
git config --global alias.co checkout
git config --global alias.lco '!f() { git checkout ":/$1:" ; }; f'

## Waste less screen estate on the prompt.
echo 'export PS1="$ "' >> $HOME/.bashrc

## Make it easy to go back and forth in the (linear) git history.
echo 'function sn() { git log --reverse --pretty=%H main | grep -A 1 $(git rev-parse HEAD) | tail -n1 | xargs git show --color; }' >> $HOME/.bashrc
echo 'function n() { git log --reverse --pretty=%H main | grep -A 1 $(git rev-parse HEAD) | tail -n1 | xargs git checkout; }' >> $HOME/.bashrc
echo 'function p() { git checkout HEAD^; }' >> $HOME/.bashrc

## Place to install TLC, TLAPS, Apalache, ...
mkdir -p tools

## PATH below has two locations because of inconsistencies between Gitpod and Codespaces.
## Gitpod:     /workspace/...
## Codespaces: /workspaces/...

## Install TLA+ Tools (download from github instead of nightly.tlapl.us (inria) to only rely on github)
wget -qN https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -P tools/
echo "alias tlcrepl='java -cp /workspace/Examples/tools/tla2tools.jar:/workspaces/Examples/tools/tla2tools.jar tlc2.REPL'" >> $HOME/.bashrc
echo "alias tlc='java -cp /workspace/Examples/tools/tla2tools.jar:/workspaces/Examples/tools/tla2tools.jar tlc2.TLC'" >> $HOME/.bashrc

## Install CommunityModules
wget -qN https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar -P tools/

## Install TLAPS (proof system)
wget -N https://github.com/tlaplus/tlapm/releases/download/v1.4.5/tlaps-1.4.5-x86_64-linux-gnu-inst.bin -P /tmp
chmod +x /tmp/tlaps-1.4.5-x86_64-linux-gnu-inst.bin
/tmp/tlaps-1.4.5-x86_64-linux-gnu-inst.bin -d tools/tlaps
echo 'export PATH=$PATH:/workspace/Examples/tools/tlaps/bin:/workspaces/Examples/tools/tlaps/bin' >> $HOME/.bashrc

## Install Apalache
wget -qN https://github.com/informalsystems/apalache/releases/latest/download/apalache.tgz -P /tmp
mkdir -p tools/
tar -zxvf /tmp/apalache.tgz --directory tools/
echo 'export PATH=$PATH:/workspace/Examples/tools/apalache/bin:/workspaces/Examples/tools/apalache/bin' >> $HOME/.bashrc
tools/apalache/bin/apalache-mc config --enable-stats=true

## Install TLAUC
wget -qN https://github.com/tlaplus-community/tlauc/releases/latest/download/tlauc-linux.tar.gz -P /tmp
mkdir -p tools/tlauc
tar -zxvf /tmp/tlauc-linux.tar.gz --directory tools/tlauc/
echo 'export PATH=$PATH:/workspace/Examples/tools/tlauc:/workspaces/Examples/tools/tlauc' >> $HOME/.bashrc

