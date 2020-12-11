package nl.ou.im9906;

import org.hamcrest.Matchers;
import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.lang.reflect.InvocationTargetException;

import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static nl.ou.im9906.ReflectionUtils.invokeStaticMethodWithParams;
import static nl.ou.im9906.ReflectionUtils.isFinal;
import static nl.ou.im9906.ReflectionUtils.isPrimitive;
import static nl.ou.im9906.ReflectionUtils.setValueByFieldNameOfFinalStaticField;
import static nl.ou.im9906.ReflectionUtils.setValueOfFinalStaticFieldByName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.hasProperty;
import static org.hamcrest.Matchers.instanceOf;
import static org.hamcrest.core.Is.is;
import static org.hamcrest.core.Is.isA;
import static org.junit.Assert.fail;

/**
 * Tests the class {@link ReflectionUtils}.
 */
public class ReflectionUtilsTest {

    @Test
    public void testIsPowerOfTwo() {
        int i = 1;
        assertThat(ReflectionUtils.isPowerOfTwo(i), is(true));
        for (int j = 0; j < 10; j++) {
            assertThat(ReflectionUtils.isPowerOfTwo(i *= 2), is(true));
        }
    }

    @Test
    public void testIsNotAPowerOfTwo() {
        int i = 3;
        assertThat(ReflectionUtils.isPowerOfTwo(i), is(false));
        for (int j = 0; j < 10; j++) {
            assertThat(ReflectionUtils.isPowerOfTwo(i *= 2), is(false));
        }
    }

    @Test
    public void testInvalidArgumentForPowerOfTwo() {
        try {
            ReflectionUtils.isPowerOfTwo(0);
            fail("Expected an IllegalArgumentException, but no exception was thrown.");
        } catch (IllegalArgumentException e) {
            assertThat(e.getMessage(), is("Method isPowerOfTwo accepts integer values >= 1 only. Illegal value: 0."));
        }
    }

    @Test
    public void testSuccessfullyInvokeStaticMethodWithParams()
            throws IllegalAccessException, NoSuchMethodException, InvocationTargetException {
        assertThat((Boolean) invokeStaticMethodWithParams(ReflectionUtils.class, "isPowerOfTwo", 5), is(false));
        assertThat((Boolean) invokeStaticMethodWithParams(ReflectionUtils.class, "isPowerOfTwo", 4096), is(true));
    }

    @Test
    public void testIllegalArgumentExceptionOnInvokeStaticMethodWitParams()
            throws IllegalAccessException, NoSuchMethodException, InvocationTargetException {
        try {
            invokeStaticMethodWithParams(ReflectionUtils.class, "isPowerOfTwo", -1);
            fail("Expected an InvocationTargetException, caused by an IllegalArgumentException, but no exception was thrown.");
        } catch (InvocationTargetException e) {
            final Throwable cause = e.getCause();
            assertThat(cause.getClass().getSimpleName(), is(IllegalArgumentException.class.getSimpleName()));
            assertThat(cause.getMessage(), is("Method isPowerOfTwo accepts integer values >= 1 only. Illegal value: -1."));
        }
    }

    @Test
    public void testGetFieldByNameAndSetFieldByName()
            throws NoSuchFieldException, IllegalAccessException {
        final AnObject anObject = new AnObject();
        ReflectionUtils.setValueByFieldName(anObject, "anInt", 1);
        assertThat((int) getValueByFieldName(anObject, "anInt"), is(1));
        ReflectionUtils.setValueByFieldName(anObject, "anInt", -1);
        assertThat((int) getValueByFieldName(anObject, "anInt"), is(-1));
    }

    @Test
    public void testGetFieldByNameAndSetFinalStaticFieldByName()
            throws NoSuchFieldException, IllegalAccessException {
        final AnObject anObject = new AnObject();
        setValueByFieldNameOfFinalStaticField(AnObject.class, "SOME_CONSTANT_INT", -1);
        assertThat((int) getValueByFieldName(anObject, "SOME_CONSTANT_INT"), is(-1));
        setValueByFieldNameOfFinalStaticField(AnObject.class, "SOME_CONSTANT_INT", 1);
        assertThat((int) getValueByFieldName(anObject, "SOME_CONSTANT_INT"), is(1));
    }

    @Test
    public void testInvokeMethodWitParameters()
            throws IllegalAccessException, NoSuchMethodException, InvocationTargetException {
        final AnObject anObject = new AnObject();
        invokeMethodWithParams(anObject, "setAnInt", 1);
        assertThat((int) invokeMethodWithParams(anObject, "getAnInt"), is(1));
        invokeMethodWithParams(anObject, "setAnInt", -1);
        assertThat((int) invokeMethodWithParams(anObject, "getAnInt"), is(-1));
    }

    @Test
    public void testIsPrimitiveField()
            throws NoSuchFieldException {
        final Object anObject = new AnObject();
        assertThat(isPrimitive(anObject, "anInt"), is(true));
        assertThat(isPrimitive(anObject, "anInteger"), is(false));
    }

    @Test
    public void testIsFinalField()
            throws NoSuchFieldException {
        final Object anObject = new AnObject();
        assertThat(isFinal(anObject, "anInt"), is(false));
        assertThat(isFinal(anObject, "anInteger"), is(true));
    }

    @SuppressWarnings({"unused", "FieldCanBeLocal"})
    static class AnObject {
        private int anInt = 0;
        private final Integer anInteger = new Integer(anInt);
        private static final int SOME_CONSTANT_INT = 0;

        private int getAnInt() {
            return this.anInt;
        }

        private void setAnInt(int anInt) {
            this.anInt = anInt;
        }

        public Integer getAnInteger() {
            return anInteger;
        }
    }

}
