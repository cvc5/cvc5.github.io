'use strict';

describe('EditorController', function(){

    // Load the module that contains the EditorController component before each test
    beforeEach(module('editor'));

    // Test the controller
    describe('EditorController', function(){

        var $httpBackend, ctrl;

        beforeEach( inject(function ($componentController, _$httpBackend_) {
            $httpBackend = _$httpBackend_;
            ctrl = $componentController('EditorController');
        }));
    });
});
