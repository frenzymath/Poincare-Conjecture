(() => {
  function redirectReference() {
    const prefix = '#/formalized-sources/';
    if (location.hash.startsWith(prefix)) {
      history.replaceState(history.state, '', location.pathname + location.search
        + '#/references/' + location.hash.slice(prefix.length));
    }
    document.documentElement.dataset.blueprintOnly =
      String(location.hash.startsWith('#/references/'));
  }
  redirectReference();
  window.addEventListener('hashchange', redirectReference);
})();
