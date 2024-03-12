const commit = [["https://github.com/leanprover-community/mathlib/blob/master/src/", "https://github.com/leanprover-community/mathlib/blob/f2ad3645af9effcdb587637dc28a6074edc813f9/src/"]];
function redirectTo(tgt) {
  let loc = tgt;
  for (const [prefix, replacement] of commit) {
    if (tgt.startsWith(prefix)) {
      loc = tgt.replace(prefix, replacement);
      break;
    }
  }
  window.location.replace(loc);
}
