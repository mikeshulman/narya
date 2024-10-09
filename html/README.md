# jsNarya: Running Narya in a browser

Here are steps to create a web page that will run Narya in a browser.  You will need the JavaScript package manager `npm`, with which you can install `typescript` and `browserify`.  With this done, run the following commands.
```
cd narya
dune build bin/jsnarya.bc.js
cd html
ln -s ../_build/default/bin/jsnarya.bc.js .
git clone git@github.com:strtok/xterm-readline.git
cd xterm-readline
echo "(window as any).Readline = Readline;" >>src/readline.ts
npx tsc
cd ..
npx browserify xterm-readline/lib/readline.js >xterm-readline.js
```
Now place the files `index.html`, `jsnarya.bc.js`, and `xterm-readline.js` in a directory that will be served by a web server.  For instance, to test it locally, you can run `npx http-server /path/to/narya/html -o -p 9999`.

The step of modifying the source code of `xterm-readline` seems like it shouldn't be necessary, but I haven't figured out the "correct" way to make it loadable in a browser.  If anyone knows, please tell me or submit a pull request.
