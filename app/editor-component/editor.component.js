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

            // editor initialization
            var editorElement = document.getElementById('editor');
            var editor = monaco.editor.create(editorElement, {
                theme: 'vs-dark',
                model: monaco.editor.createModel("", "clojure"),
                automaticLayout: false,
                fontSize: 20
            });

            var outputEditorElement = document.getElementById('outputEditor');
            var outputEditor = monaco.editor.create(outputEditorElement, {
                theme: 'vs-dark',
                model: monaco.editor.createModel("", "clojure"),
                automaticLayout: false,
                fontSize: 20
            });
            outputEditor.updateOptions({readOnly: true});
            const zoomInAction = editor.getAction('editor.action.fontZoomIn');
            const zoomOutAction = editor.getAction('editor.action.fontZoomOut');
            const zoomResetAction = editor.getAction('editor.action.fontZoomReset');
            zoomInAction.contextMenuGroupId = 'font';
            zoomOutAction.contextMenuGroupId = 'font';
            zoomResetAction.contextMenuGroupId = 'font';
            zoomInAction.keybindings = [monaco.KeyMod.Alt | monaco.KeyCode.Equal];
            zoomOutAction.keybindings = [monaco.KeyMod.Alt | monaco.KeyCode.Minus];
            zoomResetAction.keybindings = [monaco.KeyMod.Alt | monaco.KeyCode.Digit0];
            editor.addAction(zoomInAction);
            editor.addAction(zoomOutAction);
            editor.addAction(zoomResetAction);

            outputEditor.addAction(zoomInAction);
            outputEditor.addAction(zoomOutAction);
            outputEditor.addAction(zoomResetAction);

            // https://stackoverflow.com/questions/47017753/monaco-editor-dynamically-resizable
            const editorParent = editorElement.parentElement;
            const outputEditorParent = outputEditorElement.parentElement;
            window.addEventListener('resize', () => {
                // make editor as small as possible
                editor.layout({width: 0, height: 0});
                outputEditor.layout({width: 0, height: 0});

                // wait for next frame to ensure last layout finished
                window.requestAnimationFrame(() => {
                    // get the parent dimensions and re-layout the editor
                    const editorRect = editorParent.getBoundingClientRect();
                    const outputRect = outputEditorParent.getBoundingClientRect();
                    editor.layout({width: editorRect.width, height: editorRect.height});
                    outputEditor.layout({width: outputRect.width, height: outputRect.height});
                });
            });

            var errors = [];

            $scope.monacoTheme = "vs-dark";

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

            editor.getModel().setValue(defaultCode);

            //https://github.com/devuxd/SeeCodeRun/wiki/Ace-code-editor
            // editor.on("mousemove", function (e){
            //     var position = e.getDocumentPosition();
            //
            //     angular.forEach(errors, function (error) {
            //         if (position.row == error.lineNumber - 1 &&
            //             position.column == error.columnNumber - 1) {
            //             var text = error.message;
            //             if (text.length > 0) {
            //                 var pixelPosition = editor.renderer.textToScreenCoordinates(position);
            //                 pixelPosition.pageY += editor.renderer.lineHeight;
            //                 updateTooltip(pixelPosition, text);
            //             } else {
            //                 updateTooltip(editor.renderer.textToScreenCoordinates(position));
            //             }
            //         }
            //         else{
            //             updateTooltip(editor.renderer.textToScreenCoordinates(position));
            //         }
            //     });
            // });

            //https://github.com/devuxd/SeeCodeRun/wiki/Ace-code-editor
            function updateTooltip(position, text) {
                //example with container creation via JS
                var div = document.getElementById('tooltip_0');
                if (div === null) {
                    div = document.createElement('div');
                    div.setAttribute('id', 'tooltip_0');
                    div.setAttribute('class', 'ace_editor ace_tooltip tooltip_0');
                    document.body.appendChild(div);
                }

                div.style.left = position.pageX + 'px';
                div.style.top = position.pageY + 'px';
                if (text) {
                    div.style.display = "block";
                    div.innerText = text;
                } else {
                    div.style.display = "none";
                    div.innerText = "";
                }
            }

            $scope.code = editor.getModel().getValue();

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
                    editor.getModel().setValue(response.code);

                    // change the language
                    if (example.includes('smt')) {
                        $scope.parameters['lang'] = 'smtlib2.6';
                    } else if (example.includes('sygus2')) {
                        $scope.parameters['lang'] = 'sygus2';
                    } else if (example.includes('tptp')) {
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
                        editor.getModel().setValue(response.code);
                    });
                }
            }

            $scope.download = function () {

                //ToDo: remove this line
                $scope.code = editor.getModel().getValue();
                var data = new Blob([$scope.code], {type: 'text/plain'});

                // to save memory
                if ($scope.savedFile !== null) {
                    window.URL.revokeObjectURL($scope.savedFile);
                }

                $scope.savedFile = window.URL.createObjectURL(data);
            };

            function updateView(response, reset) {

                $scope.results = response;

                if (sharedService.checkNested(response, 'data')) {
                    outputEditor.getModel().setValue(response.data.join('\n'));
                } else {
                    outputEditor.getModel().setValue('');
                }


                // set decorations
                setDecorations(reset);
            }

            $rootScope.codeEmpty = function () {
                $scope.code = editor.getModel().getValue();
                if (!$scope.code || !$scope.code.trim()) {

                    $scope.results = {};
                    $scope.results.data = [
                        "Parse Error: /code.txt:1.1: Empty code"
                    ];

                    return true;
                }
                return false;
            }

            $scope.run = function () {

                if (!$scope.waitingCheck) {
                    // initialize the results
                    $scope.results = {};
                    // initialize decorations
                    setDecorations(true);

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
                } else {
                    $scope.waitingCheck = false;
                    $interval.cancel($scope.getResultInterval);
                    cvcService.cancelJob($scope.jobId);
                }
            }

            $scope.saveJob = function (jobId) {


                if (!jobId && $scope.getResultInterval) {
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

            function setDecorations(reset) {

                if (reset) {
                    errors = [];
                }

                setErrorDecorations();

                function setErrorDecorations() {
                    if (sharedService.checkNested($scope, 'results', 'data')) {
                        angular.forEach($scope.results.data, function (data) {

                            var smtLibPattern = /Parse Error: \/code.txt:\d+.\d+:.*/g;
                            var parseErrors = data.match(smtLibPattern);

                            if (parseErrors && parseErrors.length > 0) {
                                angular.forEach(parseErrors, function (parseError) {

                                    // example "Parse Error: /code.txt:10.7: Unexpected token: '('."
                                    var parts = parseError.split(':');
                                    var numbers = parts[2].split('.');

                                    var error = {};

                                    error.startLineNumber = parseInt(numbers[0]);
                                    error.startColumn = 1; // parseInt(numbers[1]);
                                    error.endColumn = 1000;
                                    error.message = parts.slice(3, parts.length).join('').trim();
                                    console.log(data);
                                    errors.push(error);
                                });
                            }
                        });
                        monaco.editor.setModelMarkers(editor.getModel(), 'test', errors);
                    }
                }
            }

            $scope.upload = function (code) {
                editor.getModel().setValue(code);
            }


            $scope.changeTheme = function () {
                monaco.editor.setTheme($scope.monacoTheme);
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
                    if (argument.type == 'int' || argument.type == 'float') {
                        $scope.parameters[$scope.selectedName] = parseInt(argument.defaultValue);
                    } else {
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
                        path: function () {
                            return $scope.path;
                        },
                        examples: function () {
                            return $scope.exampleKinds;
                        },
                        getExample: function () {
                            return $scope.getExample;
                        },
                        upload: function () {
                            return $scope.upload;
                        }
                    }
                });
            }

            $scope.onArgumentChange = function () {
                switch ($scope.parameters['lang']) {
                    case 'smtlib1':
                    case 'smtlib2.0':
                    case 'smtlib2.5':
                    case 'smtlib2.6':
                    case 'sygus1':
                    case 'sygus2':
                    case 'sygus': {

                    }
                        break;
                    case 'tptp': {

                    }
                        break;

                }
            }

        }
    ]
});