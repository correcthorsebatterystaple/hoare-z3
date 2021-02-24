const GulpClient = require('gulp');
const gulp = require('gulp');
const { execSync } = require('child_process');

function compileGrammar(cb) {
  execSync('npm run cg');
  cb();
}

exports.watch = () => {
  gulp.watch('grammar.ne', compileGrammar);
};
