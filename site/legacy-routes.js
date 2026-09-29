(() => {
  function labelReferenceContents() {
    const reference = document.documentElement.dataset.blueprintOnly === 'true';
    document.querySelectorAll('.choverview > summary').forEach(summary => {
      if (reference) summary.setAttribute('aria-label', 'Chapter contents');
      else summary.removeAttribute('aria-label');
    });
  }
  function redirectReference() {
    const prefix = '#/formalized-sources/';
    if (location.hash.startsWith(prefix)) {
      history.replaceState(history.state, '', location.pathname + location.search
        + '#/references/' + location.hash.slice(prefix.length));
    }
    document.documentElement.dataset.blueprintOnly =
      String(location.hash.startsWith('#/references/'));
    labelReferenceContents();
  }
  redirectReference();
  window.addEventListener('hashchange', redirectReference);
  // Chapters load lazily after route changes; attributes leave React's children intact.
  new MutationObserver(labelReferenceContents).observe(document.documentElement, {
    childList: true, subtree: true,
  });
})();
