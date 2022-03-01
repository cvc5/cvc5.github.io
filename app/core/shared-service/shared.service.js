'use strict';

angular.module('cvc')
    .factory('sharedService', function () {
        /**
         * to test for existence of nested object key
         * https://stackoverflow.com/questions/2631001/javascript-test-for-existence-of-nested-object-key
         */
        var checkNested = function (object) {
            var args = Array.prototype.slice.call(arguments, 1);
            for (var i = 0; i < args.length; i++) {
                if (!object || !object.hasOwnProperty(args[i])) {
                    return false;
                }
                object = object[args[i]];
            }
            return true;
        }
        return {
            checkNested: checkNested
        };
    });