'use strict';

angular.module('cvc').directive('inputFile', function ($parse) {
    return {
        restrict: "E",
        templateUrl: "core/input-file-directive/input-file.directive.html",
        scope: {
            fileChanged: "&"
        },
        link: function (scope, element) {
            element.on('change', function (event) {

                // load the content of the first file
                var file = event.target.files[0];
                if (file) {
                    var reader = new FileReader();
                    reader.onload = function (e) {
                        var content = e.target.result;
                        scope.fileChanged({text: content});
                    }
                    reader.readAsText(file);
                }
            });
        }
    };
});
