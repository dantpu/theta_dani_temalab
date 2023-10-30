package hu.bme.mit.theta.sts.analysis;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.sts.STS;

import java.util.ArrayList;
import java.util.List;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

public class Checker {
    STS sts;
    Checker(STS sts_in){
        sts=sts_in;
    }
    boolean check(){
        Solver solverbmc = Z3SolverFactory.getInstance().createSolver();
        Solver solverpathfromstart = Z3SolverFactory.getInstance().createSolver();
        solverbmc.add(PathUtils.unfold(sts.getInit(),0));
        solverpathfromstart.add(PathUtils.unfold(sts.getInit(),0));
        try (var wpp = new WithPushPop(solverbmc)){
            solverbmc.add(PathUtils.unfold(Not(sts.getProp()), 0));
            if(solverbmc.check().isSat()){
                return false;
            }
        }
        int n=1110000;
        for(int i=0;i>-1;++i){
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
            if(solverpathfromstart.getStatus().isUnsat()) return true;

            solverbmc.add(PathUtils.unfold(sts.getTrans(), i));


            //PathUtils.unfold(b,i);
            /*for(int j=0;j<i;j++){
                if (PathUtils.foldin(a.get(i),i).equals(PathUtils.foldin(a.get(j),j))){
                    int x=3;
                    return true;
                };
            }*/
            try (var wpp = new WithPushPop(solverbmc)){
                solverbmc.add(PathUtils.unfold(Not(sts.getProp()), i+1));
                if(solverbmc.check().isSat()){
                    return false;
                }
            }
        }
        return true;
    }
}
