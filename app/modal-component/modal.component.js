'use strict';

angular.module('cvc').component('modal', {
    templateUrl: 'modal-component/modal.component.html',
    bindings: {
        resolve: '<',
        close: '&',
        dismiss: '&'
    },
    controller: function () {
        var $ctrl = this;

        $ctrl.$onInit = function () {
            $ctrl.path = $ctrl.resolve.path;
            $ctrl.exampleKinds = $ctrl.resolve.examples;
        };

        $ctrl.getExampleModal = function(example) {
            $ctrl.close({$value: ""});
            $ctrl.resolve.getExample(example);

        }

        $ctrl.upload = function(text) {
            $ctrl.close({$value: ""});
            $ctrl.resolve.upload(text);
        }

        $ctrl.ok = function () {
            $ctrl.close({$value: ""});
        };
    }
});