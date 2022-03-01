'use strict';

angular.module('cvc').directive('arguments', function () {
    return {
        restrict: 'E',
        templateUrl: 'arguments-directive/arguments.directive.html',
        scope: {
            parameters: "="
        },
        controller: ['$scope', 'cvcService',
            function ($scope, cvcService) {

                // parameters
                $scope.reset = function () {
                    $scope.parameters = {};
                    $scope.parameters['lang'] = 'smtlib2.6';
                }
                $scope.reset();

                // default parameters that are always visible
                $scope.defaultParameters = ["lang"];


                $scope.search = [];
                $scope.argumentsList = undefined;
                $scope.selectedName = undefined;

                // get the list of arguments for search
                cvcService.getArguments().then(function (response) {
                    $scope.argumentsList = response;
                    angular.forEach(response, function (value, key) {
                        $scope.search.push(key + ": " + value.description);
                    });
                });

                $scope.onSelect = function ($item, $model, $label, $event) {
                    $scope.selectedName = $item.substr(0, $item.indexOf(":"));
                    var argument = $scope.argumentsList[$scope.selectedName];

                    // single argument
                    if (!argument.type) {
                        $scope.parameters[$scope.selectedName] = null;
                    }
                    // set the default value
                    else {
                        if(argument.type == 'int' || argument.type == 'float'){
                            $scope.parameters[$scope.selectedName] = parseInt(argument.defaultValue);
                        }
                        else {
                            $scope.parameters[$scope.selectedName] = argument.defaultValue;
                        }
                    }
                    // clear the selected argument
                    $scope.selectedName = '';
                }

                $scope.remove = function (key) {
                    if ($scope.parameters[key]) {
                        delete $scope.parameters[key];
                    }
                }
            }]
    };
});
