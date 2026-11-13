
// Keep Cancel attached to the proof request while /kill waits for its cleanup.
// Sending /kill through performASR would replace the Cancel target with /kill.
(function () {
    var current;
    var show = loadingScreen.show;
    loadingScreen.show = function (path) {
        current = { path: path, cancelling: false };
        show.call(this, path);
    };
    // The original proof response can arrive after /kill acknowledges cleanup.
    // Neither it nor an old /kill response may reset a replacement's controls.
    server.performASR = function (path, dataType, cache, success, error) {
        loadingScreen.show(path);
        var request = current;
        $.ajax({
            url: path,
            dataType: dataType,
            cache: cache,
            success: function (data, textStatus) {
                if (current !== request) return;
                loadingScreen.reset();
                success(data, textStatus);
            },
            error: function (data, textStatus, err) {
                if (current !== request) return;
                loadingScreen.reset();
                error(data, textStatus, err);
            }
        });
    };
    loadingScreen.cancel = function (path) {
        var request = current;
        if (!request || request.path !== path || request.cancelling) return;
        request.cancelling = true;
        $.ajax({
            url: "/kill?path=" + encodeURIComponent(path),
            dataType: "text",
            cache: false,
            success: function (data) {
                if (current === request) {
                    loadingScreen.reset();
                    ui.showDialog(data);
                }
            },
            error: function () {
                if (current === request) {
                    request.cancelling = false;
                    ui.showDialog("Unable to cancel request! Is server down?");
                }
            }
        });
    };
}());
