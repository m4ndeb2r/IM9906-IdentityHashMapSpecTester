package nl.ou.im9906;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import static nl.ou.im9906.MethodTestHelper.assertAssignableClause;
import static nl.ou.im9906.MethodTestHelper.assertAssignableNothingClause;

/**
 * Tests the class {@link MethodTestHelper}.
 */
public class MethodTestHelperTest {

    @Rule
    public ExpectedException expectedException = ExpectedException.none();

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
        expectedException.expect(AssertionError.class);
        expectedException.expectMessage("Primitive, non-assignable field 'aPrimitiveInt' unexpectedly changed.");
        assertAssignableClause(
                obj,
                "assignAll",
                new Object[]{},
                new String[]{"aPrimitiveLong", "aLongObject"}
        );
    }

    @Test
    public void testAssignFailurePrimitiveLong()
            throws IllegalAccessException, NoSuchFieldException, NoSuchMethodException {
        AnObject obj = new AnObject();
        expectedException.expect(AssertionError.class);
        expectedException.expectMessage("Primitive, non-assignable field 'aPrimitiveLong' unexpectedly changed.");
        assertAssignableClause(
                obj,
                "assignAll",
                new Object[]{},
                new String[]{"aPrimitiveInt", "aLongObject"}
        );
    }

    @Test
    public void testAssignFailureLongObject()
            throws IllegalAccessException, NoSuchFieldException, NoSuchMethodException {
        final AnObject obj = new AnObject();
        expectedException.expect(AssertionError.class);
        expectedException.expectMessage("Non-primitive, non-assignable field 'aLongObject' unexpectedly assigned.");
        assertAssignableClause(
                obj,
                "assignAll",
                new Object[]{},
                new String[]{"aPrimitiveInt", "aPrimitiveLong"}
        );
    }

    @Test
    public void testAssignableNothingFailure()
            throws IllegalAccessException, NoSuchFieldException, NoSuchMethodException {
        final AnObject obj = new AnObject();
        expectedException.expect(AssertionError.class);
        expectedException.expectMessage("Primitive, non-assignable field 'aPrimitiveInt' unexpectedly changed.");
        assertAssignableNothingClause(obj, "assignInt", new Object[]{});
    }

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
