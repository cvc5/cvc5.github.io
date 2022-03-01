'use strict';

angular.module('cvc').component('editor', {
    templateUrl: 'editor-component/editor.template.html',
    controller: ['$scope', '$http', 'cvcService', 'sharedService',
        '$interval', '$routeParams', '$location', '$uibModal', '$rootScope', 'cvcEnvironment',
        function ($scope, $http, cvcService, sharedService,
                  $interval, $routeParams, $location, $uibModal, $rootScope, cvcEnvironment) {

            // initializations
            $scope.cvcEnvironment = cvcEnvironment;
            // for examples links
            $scope.path = $location.absUrl();
            if ($scope.path.indexOf("/#") != -1) {
                $scope.path = $scope.path.substring(0, $scope.path.indexOf("/#"));
            }

            // for downloading
            $scope.savedFile = null;

            // waiting for check results
            $scope.waitingCheck = false;

            // waiting for simulate results
            $scope.waitingSimulate = false;

            // waiting for save
            $scope.waitingSave = false;

            // waiting for run
            $scope.waitingRun = false;

            // ace editor initialization
            var Range = ace.require("ace/range").Range;
            var editor = ace.edit('editor');

            var outputEditor = ace.edit('outputEditor');
            outputEditor.setReadOnly(true);
            outputEditor.setHighlightActiveLine(false);
            outputEditor.renderer.$cursorLayer.element.style.display = "none"

            var errors = [];

            $scope.isDarkTheme = true;
            editor.setTheme("ace/theme/idle_fingers");
            outputEditor.setTheme("ace/theme/idle_fingers");

            editor.getSession().setMode("ace/mode/smt_lib");
            outputEditor.getSession().setMode("ace/mode/smt_lib");

            var defaultCode = "(set-logic ALL)\n" +
                "(set-option :produce-models true)\n" +
                "(declare-fun x () Int)\n" +
                "(declare-fun y () Int)\n" +
                "(declare-fun z () Int)\n" +
                "\n" +
                "(assert (distinct x y z))\n" +
                "(assert (= (+ x y) z))\n" +
                "\n" +
                "(check-sat)\n" +
                "(get-model)\n";

            editor.setValue(defaultCode);
            editor.selection.clearSelection();

            //https://github.com/devuxd/SeeCodeRun/wiki/Ace-code-editor
            editor.on("mousemove", function (e){
                var position = e.getDocumentPosition();

                angular.forEach(errors, function (error) {
                    if (position.row == error.lineNumber - 1 &&
                        position.column == error.columnNumber - 1) {
                        var text = error.message;
                        if (text.length > 0) {
                            var pixelPosition = editor.renderer.textToScreenCoordinates(position);
                            pixelPosition.pageY += editor.renderer.lineHeight;
                            updateTooltip(pixelPosition, text);
                        } else {
                            updateTooltip(editor.renderer.textToScreenCoordinates(position));
                        }
                    }
                    else{
                        updateTooltip(editor.renderer.textToScreenCoordinates(position));
                    }
                });
            });

            //https://github.com/devuxd/SeeCodeRun/wiki/Ace-code-editor
            function updateTooltip(position, text){
                //example with container creation via JS
                var div = document.getElementById('tooltip_0');
                if(div === null){
                    div = document.createElement('div');
                    div.setAttribute('id', 'tooltip_0');
                    div.setAttribute('class', 'ace_editor ace_tooltip tooltip_0');
                    document.body.appendChild(div);
                }

                div.style.left = position.pageX + 'px';
                div.style.top = position.pageY + 'px';
                if(text){
                    div.style.display = "block";
                    div.innerText = text;
                }else{
                    div.style.display = "none";
                    div.innerText = "";
                }
            }

            $scope.code = editor.getValue();

            // tabs
            $scope.activeTab = 0; // Logs tab

            // get the list of examples
            cvcService.getExamples().then(function (response) {
                $scope.exampleKinds = response.kinds;
            });

            $scope.getExample = function (example) {

                // clear the view
                //ToDo: refactor clearing the view
                $scope.interpreterVisible = false;
                $scope.waitingCheck = false;
                $scope.waitingSave = false;
                $scope.waitingSimulate = false;
                $scope.waitingRun = false;
                $interval.cancel($scope.getResultInterval);
                updateView(null, true);

                // load the example code
                cvcService.getExample(example).then(function (response) {
                    $scope.code = response.code;
                    editor.setValue(response.code);
                    editor.selection.clearSelection();

                    // change the language
                    if(example.includes('smt')){
                        $scope.parameters['lang'] = 'smtlib2.6';
                    }
                    else if (example.includes('sygus2')){
                        $scope.parameters['lang'] = 'sygus2';
                    }
                    else if (example.includes('tptp')){
                        $scope.parameters['lang'] = 'tptp';
                    }

                    // change the syntax highlighter
                     $scope.onArgumentChange();

                });
            }

            // /#
            if ($location.hash()) {
                var hash = $location.hash();

                // /#examples/:example
                if (hash.includes('examples/')) {
                    var example = hash.replace('examples/', '');
                    $scope.getExample(example);
                }
                // /#temp_id
                else {
                    $scope.jobId = hash;
                    cvcService.getJob($scope.jobId).then(function (response) {
                        editor.setValue(response.code);
                        editor.selection.clearSelection();
                    });
                }
            }

            $scope.download = function () {

                //ToDo: remove this line
                $scope.code = editor.getValue();
                var data = new Blob([$scope.code], {type: 'text/plain'});

                // to save memory
                if ($scope.savedFile !== null) {
                    window.URL.revokeObjectURL($scope.savedFile);
                }

                $scope.savedFile = window.URL.createObjectURL(data);
            };

            function updateView(response, reset) {

                $scope.results = response;
                $scope.activeTab = 0;

                if(sharedService.checkNested(response, 'data')) {
                    outputEditor.setValue(response.data.join('\n'));
                    outputEditor.selection.clearSelection();
                }
                else {
                    outputEditor.setValue('');
                    outputEditor.selection.clearSelection();
                }


                // set annotations
                setAnnotations(reset);
            }

            $rootScope.codeEmpty = function () {
                $scope.code = editor.getValue();
                if (!$scope.code || !$scope.code.trim()) {

                    $scope.results = {};
                    $scope.results.data = [
                        "Parse Error: /code.txt:1.1: Empty code"
                    ];

                    $scope.activeTab = 0; // output tab
                    return true;
                }
                return false;
            }

            $scope.run = function () {

                if (!$scope.waitingCheck) {
                    // initialize the results
                    $scope.results = {};
                    // initialize annotations
                    setAnnotations(true);

                    if ($rootScope.codeEmpty()) {
                        return;
                    }

                    // post the code
                    cvcService.verify($scope.jobId, $scope.code, $scope.parameters)
                        .then(function (jobInformation) {
                            $scope.jobId = jobInformation.jobId;
                            $location.hash(jobInformation.jobId);
                            var reset = true;
                            $scope.waitingCheck = true;
                            // send a request after each delay
                            $scope.getResultInterval = $interval(function () {
                                    cvcService.getResults($scope.jobId)
                                        .then(function (response) {
                                            updateView(response, reset);
                                            if (reset) {
                                                reset = false;
                                            }
                                            if (response.jobFinished) {
                                                $interval.cancel($scope.getResultInterval);
                                                $scope.waitingCheck = false;
                                            }
                                        });
                                },
                                1000, // one second delay
                                $scope.parameters['timeout'] + 1, // number of attempts
                                true); // model dirty checking

                            $scope.getResultInterval.then(function () {
                                $scope.waitingCheck = false;
                            });

                        }, function onError(response) {
                            throw response;
                        });
                }
                else {
                    $scope.waitingCheck = false;
                    $interval.cancel($scope.getResultInterval);
                    cvcService.cancelJob($scope.jobId);
                }
            }

            $scope.saveJob = function (jobId) {


                if(!jobId && $scope.getResultInterval) {
                    // cancel getResults related to old jobId
                    $interval.cancel($scope.getResultInterval);
                    $scope.waitingCheck = false;
                }

                if ($rootScope.codeEmpty()) {
                    return;
                }

                $scope.waitingSave = true;
                // save the code
                cvcService.saveJob(jobId, $scope.code)
                    .then(function (jobInformation) {
                        $scope.waitingSave = false;
                        $scope.jobId = jobInformation.jobId;
                        $location.hash(jobInformation.jobId);
                    }, function onError(response) {
                        throw response;
                    });
            }

            function setAnnotations(reset) {
                var annotations;

                if (reset) {
                    annotations = [];
                    errors = [];
                    var markers = editor.getSession().getMarkers();
                    angular.forEach(markers, function (marker) {
                       editor.getSession().removeMarker(marker.id);
                    });
                }
                else {
                    annotations = editor.getSession().getAnnotations();
                }

                setErrorAnnotations();

                // sort annotations so that error annotations get displayed after other annotations
                // i.e. the order would be: warning, info, error

                annotations.sort(function (a, b) {

                    var typeA = a.type.toUpperCase();
                    var typeB = b.type.toUpperCase();
                    if (typeA > typeB) {
                        return -1;
                    }
                    if (typeA < typeB) {
                        return 1;
                    }
                    return 0;
                });

                editor.getSession().setAnnotations(annotations);

                function setErrorAnnotations() {
                    if (sharedService.checkNested($scope, 'results', 'data')) {
                        angular.forEach($scope.results.data, function (data) {

                            var smtLibPattern = /Parse Error: \/code.txt:\d+.\d+:.*/g;
                            var parseErrors = data.match(smtLibPattern);

                            if(parseErrors && parseErrors.length > 0)
                            {
                                angular.forEach(parseErrors, function (parseError) {

                                    // example "Parse Error: /code.txt:10.7: Unexpected token: '('."
                                    var parts = parseError.split(':');
                                    var numbers = parts[2].split('.');

                                    var error = {};

                                    error.lineNumber = parseInt(numbers[0]);
                                    error.columnNumber = parseInt(numbers[1]);
                                    error.message = parts.slice(3, parts.length).join('').trim();

                                    var range = new Range(error.lineNumber - 1, error.columnNumber - 1,
                                        error.lineNumber - 1, error.columnNumber);
                                    var classes = "errorHighlight row" + error.lineNumber +
                                        "column" + error.columnNumber;
                                    editor.session.addMarker(range,classes, "text");

                                    var annotationType = 'error';

                                    annotations.push({
                                        row: error.lineNumber - 1,
                                        column: 0,
                                        html: error.message,
                                        type: annotationType
                                    });
                                    errors.push(error);
                                });
                            }
                        });
                    }
                }
            }

            $scope.upload = function (code) {
                editor.setValue(code);
                editor.selection.clearSelection();
            }


            $scope.toggleTheme = function () {
                $scope.isDarkTheme = !$scope.isDarkTheme;
                if ($scope.isDarkTheme) {
                    editor.setTheme("ace/theme/idle_fingers");
                    outputEditor.setTheme("ace/theme/idle_fingers");
                }
                else {
                    editor.setTheme("ace/theme/xcode");
                    outputEditor.setTheme("ace/theme/xcode");
                }
            }

            $rootScope.setWaitingRun = function (value) {
                $scope.waitingRun = value;
            }

            // parameters
            $scope.reset = function () {
                $scope.parameters = {};
                $scope.parameters['lang'] = 'smtlib2.6';
                $scope.parameters['tlimit'] = cvcEnvironment.tlimit;
            }
            $scope.reset();

            // default parameters that are always visible
            $scope.defaultParameters = ['lang', 'tlimit'];

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
                if (Object.keys($scope.parameters).includes(key)) {
                    delete $scope.parameters[key];
                }
            }


            $scope.openModal = function () {
                // open the modal interpreter
                $uibModal.open({
                    component: 'modal',
                    resolve: {
                        path: function () {return $scope.path;},
                        examples: function () {
                            return $scope.exampleKinds;
                        },
                        getExample: function() {
                            return $scope.getExample;
                        },
                        upload: function () {
                            return $scope.upload;
                        }
                    }
                });
            }

            $scope.onArgumentChange = function() {
                switch($scope.parameters['lang'])
                {
                    case 'smtlib1':
                    case 'smtlib2.0':
                    case 'smtlib2.5':
                    case 'smtlib2.6':
                    case 'sygus1':
                    case 'sygus2':
                    case 'sygus':{
                                        editor.getSession().setMode("ace/mode/smt_lib");
                                        outputEditor.getSession().setMode("ace/mode/smt_lib");
                                 }
                                    break;
                    case 'tptp':{
                                    editor.getSession().setMode("ace/mode/tptp");
                                    outputEditor.getSession().setMode("ace/mode/tptp");
                                }
                                break;
                    {
                                    console.log('sygus');
                                }
                                break;

                }
            }

        }
    ]
});