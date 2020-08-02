package nl.ou.im9906;

import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.IdentityHashMap;

import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#maskNull(Object)} ()} method.
 */
public class IdentityHashMapMaskNullTest {

    /**
     * Tests the pureness of the method {@link IdentityHashMap#maskNull(Object)}, as
     * well as the following postcondition:
     * <pre>
     *    ensures
     *      key == null ==> \result == NULL_KEY &&
     *      key != null ==> \result == key;
     * </pre>
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     * @throws InvocationTargetException if an exception occurs during the invocation of maskNull
     */
    @Test
    public void testMaskNullNormalBehaviour()
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException, InvocationTargetException {
        final IdentityHashMap<Object, Object> map = new IdentityHashMap<>();

        assertThat((String)invokeMethodWithParams(map, "maskNull", "key"), is("key"));
        assertIsPureMethod(map, "maskNull", "key");

        final Object null_key = getValueByFieldName(map, "NULL_KEY");
        assertThat(invokeMethodWithParams(map, "maskNull", new Object[]{null}), is(null_key));
        assertIsPureMethod(map, "maskNull", new Object[]{null});
    }
}
