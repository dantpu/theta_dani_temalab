package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.utils.FpUtils;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

import java.math.BigInteger;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.TypeUtils.castFp;

public class FpRoundToIntegralExpr extends UnaryExpr<FpType, FpType> { // round to integral
	private static final int HASH_SEED = 6671;
	private static final String OPERATOR_LABEL = "fpround";

	private final FpRoundingMode roundingMode;

	private FpRoundToIntegralExpr(final FpRoundingMode roundingMode, final Expr<FpType> op) {
		super(op);
		checkNotNull(roundingMode);
		this.roundingMode = roundingMode;
	}

	public static FpRoundToIntegralExpr of(final FpRoundingMode roundingMode, Expr<FpType> op) {
		return new FpRoundToIntegralExpr(roundingMode, op);
	}

	public static FpRoundToIntegralExpr create(final FpRoundingMode roundingMode, Expr<?> op) {
		checkNotNull(op);
		return FpRoundToIntegralExpr.of(roundingMode, castFp(op));
	}

	public FpRoundingMode getRoundingMode() {
		return roundingMode;
	}

	@Override
	public FpType getType() {
		return getOp().getType();
	}

	@Override
	public FpLitExpr eval(Valuation val) {
		final FpLitExpr opVal = (FpLitExpr) getOp().eval(val);
		BigFloat value = FpUtils.fpLitExprToBigFloat(roundingMode, opVal);
		BigInteger bigInteger = value.toBigInteger();
		BigFloat round = value.round(new BinaryMathContext(bigInteger.bitLength(), opVal.getType().getExponent(), FpUtils.getMathContextRoundingMode(roundingMode)));
		round = round.round(FpUtils.getMathContext(getType(), roundingMode));
		FpLitExpr fpLitExpr = FpUtils.bigFloatToFpLitExpr(round, this.getType());
		return fpLitExpr;
	}

	@Override
	public FpRoundToIntegralExpr with(final Expr<FpType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return FpRoundToIntegralExpr.of(roundingMode, op);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof FpRoundToIntegralExpr) {
			final FpRoundToIntegralExpr that = (FpRoundToIntegralExpr) obj;
			return this.getOp().equals(that.getOp()) && roundingMode.equals(that.roundingMode);
		} else {
			return false;
		}
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	public String getOperatorLabel() {
		return OPERATOR_LABEL;
	}
}
 
