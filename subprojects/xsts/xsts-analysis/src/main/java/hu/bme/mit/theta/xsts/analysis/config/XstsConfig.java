/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xsts.analysis.config;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;

public final class XstsConfig<S extends State, A extends Action, P extends Prec> {

    private final SafetyChecker<S, A, P> checker;
    private final P initPrec;

    private XstsConfig(final SafetyChecker<S, A, P> checker, final P initPrec) {
        this.checker = checker;
        this.initPrec = initPrec;
    }

    public static <S extends State, A extends Action, P extends Prec> XstsConfig<S, A, P> create(
        final SafetyChecker<S, A, P> checker, final P initPrec) {
        return new XstsConfig<>(checker, initPrec);
    }

    public SafetyResult<S, A> check() {
        return checker.check(initPrec);
    }

}