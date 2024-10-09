const path = require('path');

module.exports = {
		entry: './src/main.js',
		output: {
				filename: 'bundle.js',
				path: path.resolve(__dirname, 'dist'),
		},
		externals: {
				'xterm': 'Terminal',
		},
		mode: 'development',
};
