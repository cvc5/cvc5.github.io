'use strict';

angular.module('cvc')
    .config([
        '$locationProvider', '$routeProvider', '$compileProvider',
        function config($locationProvider, $routeProvider, $compileProvider) {

            $locationProvider.html5Mode({
                enabled: true,
                requireBase: false
            });

            $compileProvider.aHrefSanitizationWhitelist(/^\s*(https?|ftp|mailto|tel|file|blob):/);
            $routeProvider
                .when('/',
                    {
                        template: '<editor></editor>',
                        // prevent the page from reloading when the hash is changed
                        reloadOnSearch: false
                    })
                .when('/#examples/:example',
                    {
                        template: '<editor></editor>',
                        // prevent the page from reloading when the hash is changed
                        reloadOnSearch: false
                    })
                .otherwise('/');
        }
    ]);
