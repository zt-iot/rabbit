document.addEventListener('DOMContentLoaded', function() {
    // add toggle behaviour
    document
        .querySelectorAll('.toggler')
        .forEach(function(toggler) {
        toggler.addEventListener('click', function(event) {
            event.preventDefault();

            const sourceId = toggler.getAttribute('data-source');
            const targetId = toggler.getAttribute('data-target');

            const sourceElement = document.getElementById(sourceId);
            sourceElement.classList.add('d-none');

            const targetElement = document.getElementById(targetId);
            targetElement.classList.remove('d-none');
        });
    });
});