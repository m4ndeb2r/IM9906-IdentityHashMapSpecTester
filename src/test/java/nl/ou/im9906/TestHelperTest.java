package nl.ou.im9906;

import org.hamcrest.Matchers;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.lang.reflect.InvocationTargetException;

import static nl.ou.im9906.TestHelper.invokeStaticMethodWithParams;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.hasProperty;
import static org.hamcrest.Matchers.instanceOf;
import static org.hamcrest.core.Is.is;

/**
 * Tests the class {@link TestHelper}.
 */
public class TestHelperTest {

    @Rule
    public ExpectedException expectedException = ExpectedException.none();

    @Test
    public void testIsPowerOfTwo() {
        int i = 1;
        assertThat(TestHelper.isPowerOfTwo(i), is(true));
        for (int j = 0; j < 10; j++) {
            assertThat(TestHelper.isPowerOfTwo(i *= 2), is(true));
        }
    }

    @Test
    public void testIsNotAPowerOfTwo() {
        int i = 3;
        assertThat(TestHelper.isPowerOfTwo(i), is(false));
        for (int j = 0; j < 10; j++) {
            assertThat(TestHelper.isPowerOfTwo(i *= 2), is(false));
        }
    }

    @Test
    public void testInvalidArgumentForPowerOfTwo() {
        expectedException.expect(IllegalArgumentException.class);
        expectedException.expectMessage("Method isPowerOfTwo accepts integer values >= 1 only. Illegal value: 0.");
        TestHelper.isPowerOfTwo(0);
    }

    @Test
    public void testSuccessfullyInvokeStaticMethodWithParams()
            throws IllegalAccessException, NoSuchMethodException, InvocationTargetException {
        assertThat((Boolean) invokeStaticMethodWithParams(TestHelper.class, "isPowerOfTwo", 5), is(false));
        assertThat((Boolean) invokeStaticMethodWithParams(TestHelper.class, "isPowerOfTwo", 4096), is(true));
    }

    @Test
    public void testIllegalArgumentExceptionOnInvokeStaticMethodWitParams()
            throws IllegalAccessException, NoSuchMethodException, InvocationTargetException {
        expectedException.expect(InvocationTargetException.class);
        expectedException.expectCause(Matchers.<Throwable>allOf(
                instanceOf(IllegalArgumentException.class),
                hasProperty("message", is("Method isPowerOfTwo accepts integer values >= 1 only. Illegal value: -1."))
        ));

        invokeStaticMethodWithParams(TestHelper.class, "isPowerOfTwo", -1);
    }

    @Test
    public void testGetFieldByNameAndSetFieldByName()
            throws NoSuchFieldException, IllegalAccessException {
        final AnObject anObject = new AnObject();
        TestHelper.setValueByFieldName(anObject, "anInteger", 1);
        assertThat((int) TestHelper.getValueByFieldName(anObject, "anInteger"), is(1));
        TestHelper.setValueByFieldName(anObject, "anInteger", -1);
        assertThat((int) TestHelper.getValueByFieldName(anObject, "anInteger"), is(-1));
    }

    @Test
    public void testInvokeMethodWitParameters()
            throws IllegalAccessException, NoSuchMethodException, InvocationTargetException {
        final AnObject anObject = new AnObject();
        TestHelper.invokeMethodWithParams(anObject, "setAnInteger", 1);
        assertThat((int) TestHelper.invokeMethodWithParams(anObject, "getAnInteger"), is(1));
        TestHelper.invokeMethodWithParams(anObject, "setAnInteger", -1);
        assertThat((int) TestHelper.invokeMethodWithParams(anObject, "getAnInteger"), is(-1));
    }

    static class AnObject {
        private int anInteger = 0;

        private int getAnInteger() {
            return this.anInteger;
        }

        private void setAnInteger(int anInt) {
            this.anInteger = anInt;
        }
    }

}
