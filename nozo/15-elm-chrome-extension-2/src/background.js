// Initialize extension
chrome.runtime.onInstalled.addListener(function() {
    console.log("Initializing extension...");

    // Initialize Elm program
    var app = Elm.Main.init();
});
