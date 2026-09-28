(() => {
  function redirectReference() {
    const prefix = '#/formalized-sources/';
    if (location.hash.startsWith(prefix)) {
      history.replaceState(history.state, '', location.pathname + location.search
        + '#/references/' + location.hash.slice(prefix.length));
    }
  }
  redirectReference();
  window.addEventListener('hashchange', redirectReference);
})();
