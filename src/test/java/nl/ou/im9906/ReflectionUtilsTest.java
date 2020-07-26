package nl.ou.im9906;

import org.hamcrest.Matchers;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.lang.reflect.InvocationTargetException;

import static nl.ou.im9906.ReflectionUtils.invokeStaticMethodWithParams;
import static nl.ou.im9906.ReflectionUtils.isPrimitive;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.hasProperty;
import static org.hamcrest.Matchers.instanceOf;
import static org.hamcrest.core.Is.is;

/**
 * Tests the class {@link ReflectionUtils}.
 */
public class ReflectionUtilsTest {

    @Rule
    public ExpectedException expectedException = ExpectedException.none();

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
        expectedException.expect(IllegalArgumentException.class);
        expectedException.expectMessage("Method isPowerOfTwo accepts integer values >= 1 only. Illegal value: 0.");
        ReflectionUtils.isPowerOfTwo(0);
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
        expectedException.expect(InvocationTargetException.class);
        expectedException.expectCause(Matchers.<Throwable>allOf(
                instanceOf(IllegalArgumentException.class),
                hasProperty("message", is("Method isPowerOfTwo accepts integer values >= 1 only. Illegal value: -1."))
        ));

        invokeStaticMethodWithParams(ReflectionUtils.class, "isPowerOfTwo", -1);
    }

    @Test
    public void testGetFieldByNameAndSetFieldByName()
            throws NoSuchFieldException, IllegalAccessException {
        final AnObject anObject = new AnObject();
        ReflectionUtils.setValueByFieldName(anObject, "anInt", 1);
        assertThat((int) ReflectionUtils.getValueByFieldName(anObject, "anInt"), is(1));
        ReflectionUtils.setValueByFieldName(anObject, "anInt", -1);
        assertThat((int) ReflectionUtils.getValueByFieldName(anObject, "anInt"), is(-1));
    }

    @Test
    public void testInvokeMethodWitParameters()
            throws IllegalAccessException, NoSuchMethodException, InvocationTargetException {
        final AnObject anObject = new AnObject();
        ReflectionUtils.invokeMethodWithParams(anObject, "setAnInt", 1);
        assertThat((int) ReflectionUtils.invokeMethodWithParams(anObject, "getAnInt"), is(1));
        ReflectionUtils.invokeMethodWithParams(anObject, "setAnInt", -1);
        assertThat((int) ReflectionUtils.invokeMethodWithParams(anObject, "getAnInt"), is(-1));
    }

    @Test
    public void testIsPrimitiveField()
            throws NoSuchFieldException {
        final Object anObject = new AnObject();
        assertThat(isPrimitive(anObject, "anInt"), is(true));
        assertThat(isPrimitive(anObject, "anInteger"), is(false));
    }

    static class AnObject {
        private int anInt = 0;
        private Integer anInteger = new Integer(anInt);

        private int getAnInt() {
            return this.anInt;
        }

        private void setAnInt(int anInt) {
            this.anInt = anInt;
        }

        public Integer getAnInteger() {
            return anInteger;
        }

        public void setAnInteger(Integer anInteger) {
            this.anInteger = anInteger;
        }
    }

}
