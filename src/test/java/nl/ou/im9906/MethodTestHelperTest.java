package nl.ou.im9906;

import org.junit.Test;

import static nl.ou.im9906.MethodTestHelper.assertAssignableClause;
import static nl.ou.im9906.MethodTestHelper.assertAssignableNothingClause;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;
import static org.junit.Assert.fail;

/**
 * Tests the class {@link MethodTestHelper}.
 */
public class MethodTestHelperTest {

    @Test
    public void testAssignAllSuccess()
            throws IllegalAccessException, NoSuchFieldException, NoSuchMethodException {
        final AnObject obj = new AnObject();
        assertAssignableClause(
                obj,
                "assignAll",
                new Object[]{},
                new String[]{"aPrimitiveInt", "aPrimitiveLong", "aLongObject"}
        );
        assertAssignableClause(
                obj,
                "assignInt",
                new Object[]{},
                new String[]{"aPrimitiveInt"}
        );
        assertAssignableClause(
                obj,
                "assignLongs",
                new Object[]{},
                new String[]{"aPrimitiveLong", "aLongObject"}
        );
    }

    @Test
    public void testAssignFailurePrimitiveInt()
            throws IllegalAccessException, NoSuchFieldException, NoSuchMethodException {
        AnObject obj = new AnObject();
        try {
            assertAssignableClause(
                    obj,
                    "assignAll",
                    new Object[]{},
                    new String[]{"aPrimitiveLong", "aLongObject"}
            );
        } catch (AssertionError e) {
            assertThat(e.getMessage().startsWith("Primitive, non-assignable field 'aPrimitiveInt' unexpectedly changed."), is(true));
            return;
        }
        fail("Expected am AssertionError.");
    }

    @Test
    public void testAssignFailurePrimitiveLong()
            throws IllegalAccessException, NoSuchFieldException, NoSuchMethodException {
        AnObject obj = new AnObject();
        try {
            assertAssignableClause(
                    obj,
                    "assignAll",
                    new Object[]{},
                    new String[]{"aPrimitiveInt", "aLongObject"}
            );
        } catch (AssertionError e) {
            assertThat(e.getMessage().startsWith("Primitive, non-assignable field 'aPrimitiveLong' unexpectedly changed."), is(true));
            return;
        }
        fail("Expected am AssertionError.");
    }

    @Test
    public void testAssignFailureLongObject()
            throws IllegalAccessException, NoSuchFieldException, NoSuchMethodException {
        final AnObject obj = new AnObject();
        try {
            assertAssignableClause(
                    obj,
                    "assignAll",
                    new Object[]{},
                    new String[]{"aPrimitiveInt", "aPrimitiveLong"}
            );
        } catch (AssertionError e) {
            assertThat(e.getMessage().startsWith("Non-primitive, non-assignable field 'aLongObject' unexpectedly assigned."), is(true));
            return;
        }
        fail("Expected am AssertionError.");
    }

    @Test
    public void testAssignableNothingFailure()
            throws IllegalAccessException, NoSuchFieldException, NoSuchMethodException {
        final AnObject obj = new AnObject();
        try {
            assertAssignableNothingClause(obj, "assignInt", new Object[]{});
        } catch (AssertionError e) {
            assertThat(e.getMessage().startsWith("Primitive, non-assignable field 'aPrimitiveInt' unexpectedly changed."), is(true));
            return;
        }
        fail("Expected am AssertionError.");
    }

    @SuppressWarnings({"unused", "FieldCanBeLocal"})
    static class AnObject {
        private int aPrimitiveInt = 0;
        private final Integer aFinalIntegerObject = new Integer(aPrimitiveInt);
        private static long aPrimitiveLong = 1L;
        private Long aLongObject = new Long(aPrimitiveLong);

        public void assignLongs() {
            aPrimitiveLong++;
            aLongObject = new Long(aPrimitiveLong);
        }

        public void assignInt() {
            aPrimitiveInt++;
        }

        public void assignAll() {
            assignInt();
            assignLongs();
        }

    }

}
