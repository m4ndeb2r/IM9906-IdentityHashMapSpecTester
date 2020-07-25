package nl.ou.im9906;

import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertAssignableClause;
import static nl.ou.im9906.MethodTestHelper.assertAssignableNothingClause;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#putAll(Map)}
 * method.
 */
public class IdentityHashMapPutAllTest {

    @Rule
    public ExpectedException expectedException = ExpectedException.none();

    // The test subject
    private IdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        map = new IdentityHashMap<>();
    }

    /**
     * Tests if a {@link NullPointerException} is thrown when a {@code null} is passed
     * as parameter to the putAll method of the {@link IdentityHashMap}.
     * </p>
     * JML specification to test:
     * <pre>
     *     public exceptional_behavior
     *       requires
     *         m == null;
     *       assignable
     *         \nothing;
     *       signals_only
     *         NullPointerException;
     *       signals
     *         (NullPointerException e) true;
     * </pre>
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    @Test
    public void testPutAllExceptionalBehaviour()
            throws NoSuchMethodException, NoSuchFieldException,
            IllegalAccessException, InvocationTargetException,
            NoSuchClassException {
        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Check the assignable clause
        assertAssignableNothingClause(map, "putAll", new Object[]{null});

        // Check for the NullPointerException
        expectedException.expect(NullPointerException.class);
        map.putAll(null);

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);
    }

    /**
     * TODO
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    @Test
    public void testPutAllNormalBehavior()
            throws IllegalAccessException, NoSuchFieldException,
            NoSuchMethodException, NoSuchClassException {
        // TODO: we only check the assignable clause here now. Complete this test

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Check the JML assignable clause
        final Map<String, String>[] params = new Map[1];
        params[0] = new HashMap<>();
        params[0].put("aKey", "aValue");
        assertAssignableClause(map, "putAll", params,
                new String[]{"threshold", "table", "size", "modCount"}
        );

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);
    }

}
