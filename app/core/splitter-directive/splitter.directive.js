'use strict';

angular.module('cvc').directive('splitter', function () {
    return {
        restrict: 'E',
        templateUrl: 'core/splitter-directive/splitter.directive.html',
        scope: {
            direction: '@'
        },
        controller: ['$scope', '$element',
            function ($scope, $element) {

                // hold the initial values of directions and lengths

                $scope.defaultDirection = $scope.direction;
                $scope.defaultPreviousWidth = $element[0].previousElementSibling.clientWidth/
                    $element[0].parentElement.clientWidth * 100;
                $scope.defaultNextWidth = $element[0].nextElementSibling.clientWidth /
                    $element[0].parentElement.clientWidth * 100;
                $scope.defaultPreviousHeight =  $element[0].previousElementSibling.offsetHeight /
                    $element[0].parentElement.offsetHeight * 100;
                $scope.defaultNextHeight = $element[0].nextElementSibling.offsetHeight /
                    $element[0].parentElement.offsetHeight * 100;

                // set the heights

                angular.element($element[0].previousElementSibling).css('height',
                    $scope.defaultPreviousHeight + '%');
                angular.element($element[0].nextElementSibling).css('height',
                    $scope.defaultNextHeight + '%');

                $scope.onMouseDown = function ($event) {

                    if (angular.element($event.target).hasClass('splitter')) {

                        var mouseDown = true;

                        var previous = $event.target.parentElement.previousElementSibling;
                        var next = $event.target.parentElement.nextElementSibling;
                        var parent = $event.target.parentElement.parentElement;

                        var initialX = $event.clientX;
                        var previousInitialWidth = previous.clientWidth;
                        var nextInitialWidth = next.clientWidth;

                        var initialY = $event.clientY;
                        var previousInitialHeight = previous.offsetHeight;
                        var nextInitialHeight = next.offsetHeight;

                        angular.element(parent).on('mousemove', function (event) {
                            if (mouseDown) {
                                event.stopPropagation();
                                event.preventDefault();

                                if($scope.defaultDirection == 'left' || $scope.defaultDirection == 'right')
                                {
                                    var previousNewWidth = previousInitialWidth + event.clientX - initialX;
                                    var nextNewWidth = nextInitialWidth - event.clientX + initialX;
                                    angular.element(previous).css('width', previousNewWidth + '%');
                                    angular.element(previous).css('flex', 'initial');
                                    angular.element(next).css('width', nextNewWidth + '%');
                                    angular.element(next).css('flex', 'initial');
                                }
                                else
                                {
                                    var previousNewHeight = previousInitialHeight + event.clientY - initialY;
                                    var nextNewHeight = nextInitialHeight - event.clientY + initialY;
                                    angular.element(previous).css('height', previousNewHeight + '%');
                                    angular.element(previous).css('flex', 'initial');
                                    angular.element(next).css('height', nextNewHeight + '%');
                                    angular.element(next).css('flex', 'initial');
                                }
                            }
                        });

                        angular.element(parent).on('mouseup', function () {
                            mouseDown = false;
                            window.dispatchEvent(new Event('resize'));
                        });

                        angular.element(parent).on('mouseleave', function () {
                            mouseDown = false;
                        });
                    }
                }
                $scope.hide = function ($event) {

                    $event.stopPropagation();
                    $event.preventDefault();

                    var previous = $event.target.parentElement.parentElement.parentElement.previousElementSibling;
                    var next = $event.target.parentElement.parentElement.parentElement.nextElementSibling;

                    if($scope.defaultDirection == 'left' || $scope.defaultDirection == 'right')
                    {
                        var previousInitialWidth = previous.clientWidth;
                        var nextInitialWidth = next.clientWidth;

                        var previousNewWidth, nextNewWidth;

                        if($scope.defaultDirection == 'left' && $scope.defaultDirection == 'left')
                        {
                            previousNewWidth = 0;
                            nextNewWidth = nextInitialWidth + previousInitialWidth;
                        }

                        if($scope.defaultDirection == 'left' && $scope.direction == 'right')
                        {
                            previousNewWidth = $scope.defaultPreviousWidth;
                            nextNewWidth = $scope.defaultNextWidth;
                        }

                        if($scope.defaultDirection == 'right' && $scope.defaultDirection == 'right')
                        {
                            nextNewWidth = 0;
                            previousNewWidth = nextInitialWidth + previousInitialWidth;
                        }

                        if($scope.defaultDirection == 'right' && $scope.direction == 'left')
                        {
                            previousNewWidth = $scope.defaultPreviousWidth;
                            nextNewWidth = $scope.defaultNextWidth;
                        }

                        angular.element(previous).css('width', previousNewWidth + '%');
                        angular.element(next).css('width', nextNewWidth + '%');
                    }

                    if($scope.defaultDirection == 'up' || $scope.defaultDirection == 'down')
                    {
                        var previousInitialHeight = previous.offsetHeight;
                        var nextInitialHeight = next.offsetHeight;

                        var previousNewHeight, nextNewHeight;

                        if($scope.defaultDirection == 'up' && $scope.defaultDirection == 'up')
                        {
                            previousNewHeight = 0;
                            nextNewHeight = nextInitialHeight + previousInitialHeight;
                        }

                        if($scope.defaultDirection == 'up' && $scope.direction == 'down')
                        {
                            previousNewHeight = $scope.defaultPreviousHeight;
                            nextNewHeight = $scope.defaultNextHeight;
                        }

                        if($scope.defaultDirection == 'down' && $scope.defaultDirection == 'down')
                        {
                            nextNewHeight = 0;
                            previousNewHeight = nextInitialHeight + previousInitialHeight;
                        }

                        if($scope.defaultDirection == 'down' && $scope.direction == 'up')
                        {
                            previousNewHeight = $scope.defaultPreviousHeight;
                            nextNewHeight = $scope.defaultNextHeight;
                        }

                        angular.element(previous).css('height', previousNewHeight + '%');
                        angular.element(next).css('height', nextNewHeight + '%');
                    }

                    angular.element(previous).css('flex', 'initial');
                    angular.element(next).css('flex', 'initial');

                    changeDirection();
                }

                function changeDirection() {
                    switch ($scope.direction) {
                        case 'left' :
                            $scope.direction = 'right';
                            break;
                        case 'right' :
                            $scope.direction = 'left';
                            break;
                        case 'up' :
                            $scope.direction = 'down';
                            break;
                        case 'down' :
                            $scope.direction = 'up';
                            break;
                    }
                }
            }]
    };
});
