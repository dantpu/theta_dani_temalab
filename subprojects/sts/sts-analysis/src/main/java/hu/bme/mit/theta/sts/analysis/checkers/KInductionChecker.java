package hu.bme.mit.theta.sts.analysis.checkers;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import hu.bme.mit.theta.sts.STS;

import java.util.ArrayList;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

public class KInductionChecker implements Checker{

    private final STS sts;
    private final SolverFactory solverFactory;

    public KInductionChecker(STS sts, SolverFactory solverFactory){
        this.sts=sts;
        this.solverFactory = solverFactory;
    }

    @Override
    public boolean check(){
        final Solver solverbmc = solverFactory.createSolver();
        final Solver solverpathfromstart = solverFactory.createSolver();
        final Solver solverpathfromend = solverFactory.createSolver();
        final Solver solverkinduction = solverFactory.createSolver();
        solverbmc.add(PathUtils.unfold(sts.getInit(),0));
        solverpathfromstart.add(PathUtils.unfold(sts.getInit(),0));

        try (var wpp = new WithPushPop(solverbmc)){
            solverbmc.add(PathUtils.unfold(Not(sts.getProp()), 0));
            if(solverbmc.check().isSat()){
                return false;
            }
        }
        for(int i=0;true;++i){
            solverpathfromstart.add(PathUtils.unfold(sts.getTrans(), i));
            for(int j=0; j<i; j++){
                var exprs = new ArrayList<Expr<BoolType>>();
                for(var decl: sts.getVars()){
                    exprs.add(Eq(decl.getConstDecl(i).getRef(), decl.getConstDecl(j).getRef()));
                }
                var andExpr = And(exprs);
                solverpathfromstart.add(Not(andExpr));
            }
            solverpathfromstart.check();
            if(solverpathfromstart.getStatus().isUnsat()) {
                return true;
            }

            solverpathfromend.add(PathUtils.unfold(sts.getTrans(), i));
            for(int j=0; j<i; j++){
                var exprs = new ArrayList<Expr<BoolType>>();
                for(var decl: sts.getVars()){
                    exprs.add(Eq(decl.getConstDecl(i).getRef(), decl.getConstDecl(j).getRef()));
                }
                var andExpr = And(exprs);
                solverpathfromend.add(Not(andExpr));
            }




            try (var wpp = new WithPushPop(solverpathfromend)){
                solverpathfromend.add(PathUtils.unfold(Not(sts.getProp()), i+1));
                if(solverpathfromend.check().isUnsat()){
                    return true;
                }
            }

            solverkinduction.add(PathUtils.unfold(sts.getTrans(), i));
            try (var wpp = new WithPushPop(solverkinduction)){
                solverkinduction.add(PathUtils.unfold(Not(sts.getProp()), i+1));
                if(solverkinduction.check().isUnsat()){
                    return true;
                }
            }

            solverbmc.add(PathUtils.unfold(sts.getTrans(), i));

            try (var wpp = new WithPushPop(solverbmc)){
                solverbmc.add(PathUtils.unfold(Not(sts.getProp()), i+1));
                if(solverbmc.check().isSat()){
                    return false;
                }
            }
        }
    }
}
