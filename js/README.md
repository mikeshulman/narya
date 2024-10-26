# jsNarya: Running Narya in a browser

To create a web page that will run Narya in a browser, you will need the JavaScript package manager `npm`.  Once you have this, run the following commands:
```
cd narya
dune build js/jsnarya.bc.js
cd js
npm install webpack
npm run build
```
Now place the files `js/dist/index.html`, `js/dist/bundle.js`, and  `_build/default/js/jsnarya.bc.js` in a directory that will be served by a web server.  For instance, to test it locally, you can run:
```
cd dist
ln -s ../../_build/default/js/jsnarya.bc.js .
npx http-server . -o -p 9999
```
With this, changes to the OCaml code will take effect as soon as you re-run `dune build js/jsnarya.bc.js` and reload the web page, while changes to the JavaScript side (`src/main.js`) will take effect as soon as you re-run `npm run build` and reload the web page.
