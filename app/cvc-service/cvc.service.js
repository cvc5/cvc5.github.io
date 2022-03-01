'use strict';

angular.module('cvc')
    .factory('cvcService', ['cvcEnvironment','$http', 'sharedService',
        function (cvcEnvironment,$http, sharedService) {
            

            var run = function (jobId, code, args) {

                return $http(
                    {
                        method: 'POST',
                        url: cvcEnvironment.apiUrl + "run",
                        data: {
                            jobId: jobId,
                            code: code,
                            arguments: args
                        },
                        headers: {'Content-Type': 'application/json'},
                        transformResponse: [function (data) {
                            // return the data without modification from the server
                            return data;
                        }]
                    }).then(function successCallback(response) {

                        return JSON.parse(response.data);
                    }, function errorCallback(response) {
                        throw response;
                    }
                );
            }

            var saveJob = function (jobId, code) {

                return $http(
                    {
                        method: 'POST',
                        url: cvcEnvironment.apiUrl + "saveJob",
                        data: {
                            jobId: jobId,
                            code: code
                        },
                        headers: {'Content-Type': 'application/json'},
                        transformResponse: [function (data) {
                            // return the data without modification from the server
                            return data;
                        }]
                    }).then(function successCallback(response) {

                        return JSON.parse(response.data);
                    }, function errorCallback(response) {
                        throw response;
                    }
                );
            }

            var getResults = function (jobId) {
                if (jobId) {

                    var jobUrl = cvcEnvironment.apiUrl + "getRawResults/" + jobId;
                    return $http(
                        {
                            method: 'GET',
                            url: jobUrl,
                            headers: {'Accept': 'application/json'},
                            transformResponse: [function (data) {
                                // return the data without modification from the server
                                return data;
                            }]
                        }
                    ).then(function successCallback(response) {
                            var results = JSON.parse(response.data);
                            results.data = results.data.split('\n');
                            return results;
                        },
                        function errorCallback(response) {
                            throw response;
                        });
                }
            };

            var cancelJob = function (jobId) {
                if (jobId) {
                    var jobUrl = cvcEnvironment.apiUrl + "cancelJob/" + jobId;
                    return $http(
                        {
                            method: 'GET',
                            url: jobUrl,
                            headers: {'Accept': 'application/xml, text/xml, */*; q=0.01'},
                            transformResponse: [function (data) {
                                // return the data without modification from the server
                                return data;
                            }]
                        }
                    ).then(function successCallback(response) {
                            //ToDo: review what to do with cancelJob response
                            return response.data;
                        },
                        function errorCallback(response) {
                            throw response;
                        });
                }
            }

            var getJob = function (jobId) {
                if (jobId) {

                    var jobUrl = cvcEnvironment.apiUrl + "getJob/" + jobId;
                    return $http(
                        {
                            method: 'GET',
                            url: jobUrl
                        }
                    ).then(function successCallback(response) {

                            return response.data;
                        },
                        function errorCallback(response) {
                            throw response;
                        });
                }
            };

            var getExamples = function() {

                var examplesUrl = cvcEnvironment.apiUrl + "examples";
                return $http(
                    {
                        method: 'GET',
                        url: examplesUrl
                    }
                ).then(function successCallback(response) {

                        return response.data;
                    },
                    function errorCallback(response) {
                        throw response;
                    });
            }

            var getExample = function(example) {

                var exampleUrl = cvcEnvironment.apiUrl + "examples/" + example;
                return $http(
                    {
                        method: 'GET',
                        url: exampleUrl
                    }
                ).then(function successCallback(response) {

                        return response.data;
                    },
                    function errorCallback(response) {
                        throw response;
                    });
            }

            var getArguments = function() {

                var argumentsUrl = cvcEnvironment.apiUrl + "arguments";
                return $http(
                    {
                        method: 'GET',
                        url: argumentsUrl
                    }
                ).then(function successCallback(response) {
                        var data = response.data;
                        angular.forEach(data, function (value, key) {
                            if(value.type =="bool" && value.alternate){
                                data["no-" + key] = data[key];
                            }
                        });
                        return data;
                    },
                    function errorCallback(response) {
                        throw response;
                    });
            }


            return {
                verify: run,
                getResults: getResults,
                cancelJob: cancelJob,
                getJob: getJob,
                saveJob: saveJob,
                getExamples: getExamples,
                getExample: getExample,
                getArguments: getArguments
            };
        }]);